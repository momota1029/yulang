# Sprint NATIVE-INTEGER-COMPARISON-AUDIT-INTEGRATION-20261026/r42

Status: READY; Luna owns isolated verification and conditional integration; one fresh reviewer after freeze.
Branch: `research/simple-sub-intrusion`
Baseline: `9c104326a8ee688ec98a1f26bb5f700ad3fa85ca`

## Fixed outcome

Repair R41's BLOCKING evidence gap by producing a durable exact audit source and complete Lean output for all 23 frozen r8 theorem declarations. After a fresh independent delta review of that evidence and the one-line root import, promote the unchanged candidate into `YulangClosure.lean` and verify the default `YulangClosure` target in an isolated checkout. Copy only byte-identical reviewed outputs and the reviewed root file into the primary worktree. This packet is authorized independently of R40; R40 remains FAILED because its 14-call cap was exceeded. Do not reinterpret that violation or carry any R40 budget.

This closes only the signed-decimal comparison/readback slice if every gate passes. Full source/native execution, producer correctness beyond the existing invariant, other primitives, whole executor, inference A/B and production remain OPEN.

## Frozen inputs and exact base

- R40 candidate `notes/theory/lean/YulangClosure/NativeIntegerComparison.lean`: SHA-256 `2352602b7047611e9f9722d788ed1acdf9f4960d178c48f6a08b1a7054f93e79`.
- R40 worker handoff: `tasks/agent-loop/inbox/native-integer-comparison-r40.md`, `e293493a396f834a147dfb16c206e56ddb0aa7fd938ede016f65adc9b693b7d3`.
- R40 primary receipt: `tasks/agent-loop/inbox/native-integer-comparison-r40-primary-verification.txt`, `bbd43b91179fa278f248d29bb693b7bb314222d1966ad9d85380b4a79dccf050`; it has grouped results but not complete output. Preserve it unchanged.
- R40 incomplete scratch audit: `notes/theory/lean/.lake/native-integer-comparison-r40-audit.lean`, `2ab35bb0b8c428e4e016a910fbcb0fc2cf456001e32f1f022841b8a91e2506ac`.
- R41 contract `8ade6bdd4ff7697d7443a349f0f75a71c774e0681ff40276da5494bc296ea070`; R41 review `tasks/agent-loop/inbox/native-integer-comparison-r41-review.md`, `71cfd3d1ccf9e508ff512d75070fb47a2e043f37599850922d3c244a5d20047a`. R41 found no source/math branch divergence and the exact audit evidence defect.
- Manuscript: `docs/yulang-operational-type-safety-ja.tex`, `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`. Readback: `notes/theory/lean/YulangClosure/NativeLiteralReadback.lean`, `53a745397fed4b319225541b8e764a32cdc72032ca4e8be48d9d4a23d3901c54`. Producer invariant: `notes/theory/2026-10-25-native-literal-producer-invariant.md`, `1f73d0a4e221cb2d2a182876cf9928ebd3cab34edd6d36f4a46bb6bd3ca9a651`.
- Rust decimal source `83ba443036c7da05f9d72d4bbba98b05c4cab2135062743ffe8e3f05250d1cae`, machine consumers `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`, HIR mapping `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`.
- Toolchain/project: Lean pin file `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; `lakefile.toml` `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`; manifest `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`; root base `YulangClosure.lean` `aeb4b99af2a786363446c49a07cf1df4ac631c411c93305b110f6868078b8641`.

## Verification and integration plan

Use a fresh detached worktree at `9c104326a8ee688ec98a1f26bb5f700ad3fa85ca` under the exact Luna-only path `/tmp/yulang-r42-native-integer-20261026`. Do not reuse or write R40's `.lake` cache. Copy the candidate into the same module path only after its SHA matches. All scratch/cache output stays inside this isolated checkout and is discarded only after verified copies are preserved in the leased primary receipt.

Luna performs at most five Lean/Lake process invocations, sequentially, no more than 180 cumulative checker seconds, 120 seconds each, one process at a time: (1) native Lake version; (2) pinned `lake env lean --version`; (3) build `+YulangClosure.NativeIntegerComparison`; (4) execute the durable uniquely named audit source; (5) after successful audit, add only `import YulangClosure.NativeIntegerComparison` to the isolated root and build the default `YulangClosure` target. No scratch diagnostics or retries. Stop on the first mismatch, failure, timeout or limit.

The exact audit source is embedded as a fenced Lean block at the start of `tasks/agent-loop/inbox/native-integer-comparison-r42-primary-verification.txt`; Luna materializes those exact bytes as an isolated scratch source and records its hash. It imports the candidate and, in order, verifies each of the following fully qualified declarations is a theorem, prints its complete type and `#print axioms`, and enforces a strict whitelist `{propext, Quot.sound}` with `Lean.collectAxioms`: `fold_expansion`, `fold_zero`, `parseBytes_success_iff`, `parts_success_iff`, `parts_reject_iff`, `trim_spec`, `normalize_spec`, `value_bound`, `value_lower`, `block_lt`, `compare_add_prefix`, `lex_value`, `shorter_value`, `magnitude_value`, `compareParts_value`, `parts_spec`, `compare_decode`, `boolean_projections`, `intEq_decode`, `intLt_decode`, `intLe_decode`, `intGt_decode`, `intGe_decode`. Persist the full untruncated stdout/stderr with exact commands, exits and durations in the same verification receipt; also include the audit source bytes and its hash, tied to candidate/root hashes. The receipt carries the handoff fields, so no separate R42 handoff file is needed. Do not claim complete audit from a summary or from the old scratch theorem. Scan the exact candidate for holes, project axioms and checker bypasses; record the scan.

After the five primary calls succeed, freeze hashes and launch one fresh `compiler_referee` to review only the exact candidate, embedded audit source/output and isolated root import. It writes only `tasks/agent-loop/inbox/native-integer-comparison-r42-review.md`; checker/build/test calls are forbidden to the reviewer. Review grant: at most 180 active seconds, conservatively charge full if exact duration is unknown. Any blocking/major finding stops integration. Only after a CLEAN review may Luna copy the exact candidate, verification receipt (including audit source/output) and reviewed root file bytes into the primary worktree, update current state, and remove the isolated worktree. Recheck hashes, do not run more Lean calls in the main worktree.

## Exact primary/reviewer leases and stop conditions

Primary owns: `tasks/agent-loop/sprints/native-integer-comparison-audit-integration-r42.md`, `tasks/agent-loop/current.json`, `notes/theory/lean/YulangClosure.lean`, `notes/theory/lean/YulangClosure/NativeIntegerComparison.lean` (copy only), `tasks/agent-loop/inbox/native-integer-comparison-r42-primary-verification.txt`. Isolated checkout, audit, root edit and `.lake/build` are also Luna-only exact outputs. Reviewer owns only `tasks/agent-loop/inbox/native-integer-comparison-r42-review.md`. Children do not start teams, change authority, or perform Git. Pending question directories remain fully unstaged/uncommitted.

Fresh grant: 900 active seconds for Luna including at most five invocations and 180 checker seconds; reviewer at most 180 seconds; no Rust/Cargo/tests. R41's 300 seconds and R40's 900/600/300 grants are not carried. Success requires exact frozen hashes, complete 23 type/axiom outputs within the strict whitelist, successful isolated root build, independent CLEAN delta review, and Luna's primary integration receipt.
