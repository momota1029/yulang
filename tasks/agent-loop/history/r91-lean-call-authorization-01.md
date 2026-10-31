# R91 Lean call 1 — frozen-input review and authorization

This record authorizes the primary's first direct Lean call for the admitted R91 proof packet. It was committed and pushed before execution, as required by the R91 contract.

## Frozen inputs

- Contract `tasks/agent-loop/sprints/effect-permission-formal-registration-supplier-20261101-r91.md`: SHA-256 `4f64c5905cd03a2f377a152259d57a846f58834a9ab4669584ccd67e16fefdad`.
- Manifest `tasks/agent-loop/sprints/effect-permission-formal-registration-supplier-20261101-r91-inputs-r1.json`: SHA-256 `2f2c024aae812057364e880238be072a1e63398fe31fde94d4c269e19a048844`; all 93 unique paths match.
- Candidate `notes/theory/lean/YulangClosure/OriginalFormalRegistrationSupplierR91.lean`: 14,816 bytes, SHA-256 `d5187d6dce15a3c6a8979c5e6e88a097fcd7815a53fc81ed4770fd137750de2b`.
- Proof handoff `tasks/agent-loop/inbox/effect-permission-formal-registration-r91-proof.md`: 15,452 bytes, SHA-256 `6c0b39ceb12527d2d336238b846a1171d8288b3bddafd84a724ec9a1afc6bd26`.
- Flattened stdin: 934,982 bytes, SHA-256 `d0b42e35ea434d79f41d56a7788c30a9cd3d71bbd5cecc0111b32903b10044c4`.

The initial assigned handoff hash `96dcc09abf4446fb09604f2c40b2831d6beb6cd3cf94d966a0ce51cd24792844` was superseded by the proof writer's final frozen handoff above before this review. The independent reviewer was notified and reviewed the final hash.

## Independent pre-execution review

Reviewer `/root/r91_preexecution_review` returned **PASS** on the final frozen candidate and handoff. The reviewer independently matched the manifest (93/93), candidate and handoff hashes, and flattened-input length/hash; verified dependency order and byte-preserving flattening; and found no blocking, major or minor compiler-correctness finding. The reviewer confirmed that the declarations construct the selected formal contract through actual Shared delivery, keep actual annotated Name/App premises under one App witness, and do not assume the missing declaration-to-use equality. The permissive EventProof overwrite is explicitly only an interface discriminator, not a supported-source counterexample. The full review receipt is the independent agent's final report in this session.

## Exact call authorization

Authorized: one primary-owned direct invocation of `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`, working directory `notes/theory/lean`, with `LEAN_NUM_THREADS=1`, one thread, and a hard timeout of 120 seconds. Feed only the exact flattened stdin above. Capture complete stdout and stderr in process memory and record their lengths and SHA-256, exit status, elapsed time, executable version/hash, every emitted theorem type, and every complete axiom report. No Lake, build, test, cache, scratch file, worktree, or environment is authorized. This is call 1 of at most 2; no call has yet been made at this authorization point.

This authorization concerns kernel checking only. It does not close the original formal registration supplier, declaration-to-use preservation, complete Call formation, native correspondence, original A/B, or production readiness. The first missing source-owned admission/readout law and both-mode Name contract interpretation remain open as recorded in the proof handoff.
