# Amendment 01 — repair admitted source baseline and target native reconstruction

Parent contract: `SELECTED-MODULE-ENTRY-AND-FRESHENING/r1`
Revision status: ACTIVE after primary adjudication of the rejected baseline review.
This amendment preserves the original source domain, theorem quantifiers, expected outputs, semantics, production boundary and total envelope. It changes only the Rust work location/repair target and the independent proof target in response to authenticated findings and the selector's boundary recommendation.

## Authenticated decision inputs

- Base contract: `tasks/agent-loop/sprints/selected-module-entry-freshening-20261028-r1.md`, SHA-256 `1091467e92e7231bc416190eb9c0727d39fadfdcafcbc78a2c1dcd4b26e40fb2`.
- Rejected baseline review: `tasks/agent-loop/inbox/selected-module-entry-freshening-review.md`, SHA-256 `ed3dc72a7c1ab1301294a5e9822f2251273d1656d775ae5db726ff08b09ec3c9`. Disposition REJECT; defects: changed original `= pair` regression into recursive `= f pair`; test trace panics when a symbolic memo path lacks a constructor identity.
- Selector disposition: `/root/r3_selector`, recommending isolated repair, retention of H_u as AUTHORITY_BLOCKED, and a native freshening reconstruction target.
- Source authority: `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–5, SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- Selection authority: `notes/design/2026-10-08-source-generalize-definition.md`, SHA-256 `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`.
- Original-generation §7.2: `notes/theory/2026-10-17-ordinary-call-original-generation.md`, SHA-256 `bd2a690517118c8826dfe1a2fe9db53c829a1638bd2e6a1fd5aa01a252735aab`; its proposed constructor is not adopted authority.
- Handle-introduction obstruction: `notes/theory/2026-10-17-module-source-handle-introduction.md`, SHA-256 `df0e684bad2da05741e39db12bd06bb400ad8b5b15af4116abab4df6c9df06c3`.
- Rejected overlay snapshot: `/tmp/selected-module-entry-rejected-overlay-r1.patch`, SHA-256 `11f7623ff495f896dc36a6499e57fe5dd0fd12a7429777f40be22011c43707ce`, 73,818 bytes. This is a repair starting point only, not admitted evidence.

## Rust repair assignment

Primary-created isolated worktree: `/tmp/yulang-selected-module-freshening-repair-r1`, detached at authenticated committed base `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`. The rejected patch was applied there byte-for-byte as the starting overlay. Initial source hashes were authenticated:

- `crates/yu-solver/src/candidate_effect.rs`: `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`.
- `crates/yu-solver/src/candidate_scheme.rs`: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`.

The implementer may write only those three source files inside that worktree and its exact handoff `tasks/agent-loop/inbox/selected-module-entry-freshening-repair.md` there. Do not edit the shared root tree, runtime paths, other owners, the rejected snapshot, or any central state. No Git operations. No build, Cargo, tests, or Lean before the complete repaired delta receives a fresh independent review and explicit primary admission.

Required repair and evidence:

1. Restore the predecessor's nonrecursive source fixture `my f(pair:((int -> [io] ()), (int, int -> [io] ()))) = pair` and the original `tuple_formal_permissions_keep_element_paths_and_transaction_ownership` test/assertions from authenticated base bytes. Keep a recursive transport probe separately; do not claim it replaces the original regression.
2. Remove the panic precondition from test-only trace recording. Missing constructor identity must be handled without inventing an ID; memo results and solver behavior must remain unchanged. Cover formal-entry annotation, local annotation and computation routes that share the memo helper.
3. Report an exact feature-correct Cargo argv to primary for later authorization. Do not execute it during repair. Include complete three-owner net diff SHA, relevant added/changed test names, omitted cases and a writes-stopped receipt.

Repair ceiling: 600 seconds, charged within the remaining envelope. No automatic renewal.

## Proof assignment — native reconstruction only

The previous typed-entry/H_u target is superseded for this assignment and remains **AUTHORITY_BLOCKED**. Occurrence coordinates, a provider's `Occurrences`, a publication record, a proposed constructor, or successful native routing do not establish an owning typed-entry constructor. Do not assume `LocalLaws`, introduce generic supplier assumptions, or narrow the original claim.

Prove or precisely reduce the native equation: the returned freshening lower equals reconstruction `Phi_u` of the captured graph root under the actual retained fresh-use maps, including all dependent fields, original scopes and shared witnesses. Inspect the cited source definitions and the exact Lean definitions/dependencies before constructing a theorem. If the declarations or source correspondence do not support the equation, preserve the first precise missing premise instead of fabricating a bridge. Keep the separate equation identifying that graph with the original whole branch allocation root OPEN; apply every useful result to the original obligation and name that remaining owner.

Exact outputs:

- `notes/theory/lean/YulangClosure/FormalPermissionFresheningReconstruction.lean`
- `tasks/agent-loop/inbox/selected-module-entry-freshening-reconstruction-proof.md`
- sole build/cache owner: `notes/theory/lean/.lake/build`
- task-local checker scratch: `notes/theory/lean/.task-tmp-selected-module-freshening-r1/` (set `TMPDIR` to this exact directory for checker-created temporary audit files)

Read-only governing inputs are the seven exact authority/contract/receipt paths and hashes above, `notes/theory/lean/lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `README.md`, `.agents/skills/yulang-lean-proofs/references/sources.md`, `.agents/skills/yulang-lean-proofs/references/execution.md`, and only the exact source/Lean dependency files needed after search. Pin all inspected dependencies in the handoff. Do not touch the old unmaterialized proof leases `FormalPermissionSelectedModuleEntry.lean`, `FormalPermissionFresheningImage.lean`, or the old proof handoff; those received zero writes/Lake invocations and are retired by this amendment.

The prior proof grant of 1,000 seconds was issued and fully charged to r1 before any Lean invocation or file write. It is not reset or refunded. This continuation may use at most the unspent portion of that same 1,000-second grant; primary must stop it at the earlier of 600 seconds active work or the verified remaining amount. Do not issue a new proof grant. One verifier owns the cache. Lean version must match pinned 4.35.0; preserve all logs and report theorem types and full transitive axiom audits for each checked declaration. Proof output is conditional/candidate unless its source/native dependencies are established.

## Review, budget and gates

Fresh complete-delta independent review of the repaired Rust bytes is capped at 300 seconds and has an amendment-specific output path owned by primary. The reviewer must first validate fixture restoration, then trace-safety across all three paths, full diff against the pinned base, cfg/feature coverage and no changed solver behavior. Review is read-only and must not run tests/builds/Cargo/Lean. Only after a PASS may primary admit the repaired source baseline and authorize a separately receipted feature-correct Cargo verification attempt.

Original r1 envelope is 3,600 seconds and is not reset. Accounting at amendment: baseline review grant 300 seconds charged; initial proof grant 1,000 seconds charged/reserved before pause; total 1,300 charged, 2,300 unallocated. Remaining allocation: repair 600, final independent review 300, primary coordination/integration/verification 1,000, contingency 400. The proof continuation is drawn only from its already charged 1,000-second grant and adds zero to unallocated time. Every later attempt is bounded by the contract's heavy-check limits and one verification owner. No additional grant or timeout retry is implied.

The Rust baseline remains REJECTED until independent review and explicit admission. Original parent, H_u, source/native whole-branch correspondence, A/B, effect-hygiene and production gates remain OPEN. No counterexample to the language theorem is established. Unknown worker rows, quarantined runtime paths, pending questions and all other leases remain unchanged.
