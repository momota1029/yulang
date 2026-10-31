# R91 Lean call 2 — corrected frozen-input review and authorization

This record authorizes the primary's second and final permitted direct Lean call for the R91 proof packet. It supersedes only the failed input-flatten recipe in call authorization 01; the frozen candidate and theorem statements are unchanged.

## Corrected frozen input

- Candidate `notes/theory/lean/YulangClosure/OriginalFormalRegistrationSupplierR91.lean`: 14,816 bytes, SHA-256 `d5187d6dce15a3c6a8979c5e6e88a097fcd7815a53fc81ed4770fd137750de2b`.
- Corrected flattened stdin: 934,946 bytes, SHA-256 `54333b38794858ce2dccd2c8a44f1aa1a1c4ee8832964e3307c791c223a8ae44`.
- Exact 22-file order, source paths, source hashes, contract and manifest remain those recorded in `effect-permission-formal-registration-r91-proof.md` and call authorization 01.

The corrected recipe retains the first `import Std` from `OriginalSourceSyntax.lean` at line 1, removes every other line beginning `import ` (all internal `YulangClosure` imports plus the three redundant `import Init` lines), preserves every other source byte and line ending, and joins the 22 complete bodies with one LF byte. All 22 files end in LF. The only remaining import is the initial `import Std`.

## Independent corrected-input review

Reviewer `/root/r91_preexecution_review` independently reconstructed 22 bodies and the exact corrected length/hash. It verified there are no remaining mid-file `import`, `public import`, `prelude`, or `module` commands, that `Init` is available through Lean's implicit initial import, that declaration and audit commands retain their positions, and that all non-import bytes, source ordering and the candidate hash remain unchanged. **PASS** for the corrected pre-execution recipe. The reviewer explicitly withdrew the prior PASS for the obsolete input; it did not validate that input.

## First-call failure retained

Call 1 used the obsolete 934,982-byte input (SHA-256 `d0b42e35ea434e79f41d56a7788c30a9cd3d71bbd5cecc0111b32903b10044c4`) and exited 1 in 14.786 seconds at `<stdin>:2375:0` with the header-only import error recorded in `r91-lean-input-flatten-correction-01.md`. It produced no declaration, type, or axiom result. The prior reviewer's first PASS was withdrawn after this error; the corrected input received a separate independent PASS.

## Exact call authorization

Authorized: the second and final primary-owned direct invocation of `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`, working directory `notes/theory/lean`, with `LEAN_NUM_THREADS=1`, one thread and a hard timeout of 120 seconds. Feed only the corrected flattened stdin above. Capture stdout/stderr in process memory and record lengths and SHA-256, exit status, elapsed time, executable path/hash, every emitted theorem type, and every complete axiom report. No Lake, build, test, cache, scratch file, worktree, or environment is authorized. This call consumes the final slot of the two-call cap.

No closure beyond actual kernel checking follows. The source-owned admission/readout law, complete original supplier, both-mode contract-to-Name interpretation, complete Call, native correspondence, original A/B, and production readiness remain open.
