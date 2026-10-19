# Sprint effect-hygiene-executable-method-role-20261019-r78 — decision-ready pilot correction

Status: CANDIDATE — exact selector delta and Luna supplemental activation pending  
Revision: 2; preserves R78 rev1, its proof, and both independent review receipts unchanged  
Branch / baseline: `research/simple-sub-intrusion` / `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Rev1 contract SHA-256: `bf68454c19a7b4cfe5168355e0e5fb73beec069ad57dd53678258a66f26dfcab`

## Parent, prior proof and exact reason for revision

The original Simple-sub theorem, evaluator and A/B obligations remain OPEN 0→0; R50 remains NOT_ADOPTED. R78 rev1 proof stays frozen OPEN/UNFINISHED at the unaudited raw-source→LocalSource producer; its conditional three-fixture runtime trace does not establish native K/D, a residual type, continuation resumption, or universal hygiene. Do not restart proof or extend it into storage/fiber work.

Fresh rev1 spec review found a major gap: required missing/ambiguous/callable-field/effectful examples had only prose, and the reject list classified valid behavior as rejection. It also found that receiver/argument wording did not delimit charter §21 Value/Computation entry. Fresh compiler review found a major owner-path gap: role/impl members are not materialized as executable members; Apply lowering does not give `RuntimeProgram` a selected callee identity or admit role/impl metadata. Full inline findings are preserved in `current.json`; reviewer workers are STOPPED. Rev1 design/readiness/handoff artifacts remain immutable.

## Rev2 outcome and success evidence

Produce a decision-ready **document-only** method/role pilot design revision and handoff. It makes no semantic choice authoritative and grants no implementation/code/test permission. The frozen rev1 proof is supporting bounded evidence only; it remains OPEN/UNFINISHED.

The revised pilot must contain exact source examples and expected proposed outcomes for: unique role-backed method; absent target; ambiguity across roles; callable field collision; effectful receiver and argument; computation-annotated formal retention; and an outward method-body request. Separate valid execution behavior from source diagnostics and from provisional-playground unavailability. These examples remain Draft and unapproved.

Reconcile all call entry with approved charter §21: argument computations are constructed inertly; Value formals force/rebind once at the receiving activation before the body, even when unused; explicit Computation formals retain the carrier for source consumption. No blanket eager execution or tag-based role selection. If the proposal changes this, name it as a new choice requiring user approval and supersession.

Write the complete hypothetical path and owners: parser nodes; source-owned role/impl/member identities; declaration admission; role signature and impl body validation; executable member source root/environment; unique selected callee identity tied to the exact impl/member; ordinary application elaboration with provenance; `CandidateInference` admission; and `RuntimeProgram` treatment of validated declaration metadata. State how malformed declarations are diagnosed, and how unsupported-but-valid or unvalidated declarations are refused by the provisional executable-admission path; do not silently turn playground unavailability into a language diagnostic. Do not use a bare spelling such as `second` as executable identity. Do not infer that Apply or current playground support completes source typing or execution correspondence.

Before/after: rev1 had a surface proposal with an incomplete execution path and missing negative/effect examples. Rev2 must provide an owner-complete cutover design with a concrete case matrix, entry-role behavior, unique callee provenance, and every remaining implementation/proof obligation named. Independent fresh compiler/source and spec/design delta reviews must find no unresolved blocking/major issue for this design-readiness claim.

## Exact new dependencies

Read these pinned owners for the rev2 design only; no source write lease follows:

- `crates/yu-hir/src/shadow.rs` SHA-256 `9bf3e046a55206607527d2df3dde42b32afa814bc8d8b82c814583923aefc856`.
- `crates/yu-hir/src/module/local_source.rs` SHA-256 `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`.
- `crates/yu-hir/src/module.rs` SHA-256 `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a`; `crates/yu-hir/src/lib.rs` SHA-256 `afd9b382d95e2a8d22635eaf6b9bd8f134b80f5ebd35789265e236884b0fa58e`.
- `crates/yu-syntax/src/declaration/role_decl.rs` SHA-256 `0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634`.
- `crates/yu-solver/src/shadow_apply.rs` SHA-256 `b28193a5141b019afd6e10766dd77f86366f7a3c04e822b2a4fce784673b665b`; `crates/yu-solver/src/lib.rs` SHA-256 `b90eeb2ce7ff78731ce418313fd9fb54b91283d90ae6462723186fde5c0045b0`.
- `crates/yu-solver/src/candidate_source.rs` SHA-256 `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` (source-admission and placeholder preflight owner delegated to by `shadow_apply.rs`).
- `tools/inference-playground/src/runtime/program.rs` SHA-256 `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11`; `machine.rs` SHA-256 `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46`.

Retain all unchanged R78 rev1 authority, syntax, runtime, proof and fixture pins from the activation receipt. Recheck all listed hashes before authoring. If any differs, stop and return to Luna before reading/using changed bytes.

## Exact new leases and outputs

Luna alone owns:

- `notes/design/2026-10-19-r78-executable-method-role-pilot-rev2.md`
- `notes/progress/2026-10-19-r78-surface-readiness-rev2.md`
- `tasks/agent-loop/inbox/20261019-r78-implementation-rev2.md`
- this rev2 contract, `tasks/agent-loop/current.json`, and `notes/progress/2026-10-19-r78-closeout.md`

Fresh compiler/source reviewer owns only `tasks/agent-loop/inbox/20261019-r78-r2-compiler-review.md`; fresh spec/design reviewer owns only `tasks/agent-loop/inbox/20261019-r78-r2-spec-review.md`. If these read-only roles prohibit artifact writes, Luna records inline verdicts with artifact target hashes and STOP provenance. No old reviewer is reused as self-review; use fresh identities.

The proof note/handoff, rev1 design/progress/handoff and inline review receipts stay frozen. No code, syntax, HIR, solver, runtime, test, expected-output or fixture path is leased. No test/probe/build/CLI command is authorized.

## Resource supplement, reviews and stop

Luna issues one fresh **1200-second supplement**: Luna design/readiness/handoff 600s, fresh compiler delta review 300s, fresh spec delta review 300s. This raises the R78 cap from 3600s to 4800s, still below the 7200-second default. Preserve the 300-second integration reserve. Charge all unknown rev1 author/reviewer time at their full issued allocations; no refund or carryover. The already stopped proof remains charged at its full 900-second allocation. Do not imply extra unmeasured capacity.

Freeze rev2 artifacts and direct hashes before review. Reviewers inspect the exact rev2 source-owner pins, rev1 proof with its OPEN limits, rev2 design, and all concrete examples. A blocking/major finding, hash drift, exhausted supplement, or missing owner stops acceptance; record OPEN/UNFINISHED without another retry. No proof restart, semantic adoption, source edits, tests, or production promotion is permitted.

On success, close only the decision-ready design milestone. Present exact semantic choices for user decision before preparing any implementation contract. Parent/evaluator/A-B remain OPEN 0→0; R50 remains NOT_ADOPTED.
