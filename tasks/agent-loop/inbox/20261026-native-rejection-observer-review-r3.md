# Independent review: exact rejecting-source observer

Date: 2026-10-26. Producer/integrator: `/root`.
Independent reviewer: `/root/original_recursive_closure_r3`.
Review window: 16:44:02–16:47:01 UTC, within the 15-minute read-only budget.

**PASS, no blocking, major or correction findings.** Scope: the frozen
five-file observation packet, its reproduction and its stated limitations.
No original-source validity, abstract intrusion qualification, global
soundness, principality or termination conclusion is certified here.

## Reviewed bytes

| Artifact | SHA-256 |
| --- | --- |
| `2026-10-26-original-direct-return-native-rejection.md` | `4de843048215bfe9ab20faa7037079d53233930d9295fd9ab08e7eb61c27b494` |
| `2026-10-26-direct-return-aliased.yu` | `74cc1412fd1d5fc44713567756190439cbbd7168023d8f85d14899059d73b617` |
| `2026-10-26-native-observer.patch` | `99c3a3f402381581820c706cb1748b7216d67cb3d50ebf9193959a68e1216fb3` |
| `2026-10-26-native-observer.rs` | `ddd76375b35894f768acfa18a05cc8aad8eca27ad12f0b25b54ec624e87b6b0c` |
| `2026-10-26-prepare-native-observer.py` | `023d8d5acc10f3a23d44063ee32a42bf6abffeafd67a54274eea6b07a7bc256f` |

## Independent checks

The patch changes only four private-copy files: existing trace points,
immutable dispatch readouts, a separate observation counter and an explicit
cutoff. It adds no solver-state update, constraint, routing decision or
result manipulation. Allocation/timing overhead remains explicitly outside
any claimed equivalence. Both original and observed `shadow_apply.rs` have
SHA-256 `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d`;
the conflict guards still return ArtifactMismatch on intrusion/graph export.

The preparation script requires a new directory outside the repository,
checks native input bytes, copies tracked solver content from HEAD and only
patches that copy. The original and patched hashes match preparation.json.
Dependency path changes affect only the private manifest. A read-only lock
comparison confirms all 22 registry packages retain their original version,
source and checksum. The script does not build or run inference itself.

The exact trace events listed in the note were checked against the newly
prepared copy's run.trace: row38's initial level 2; merge 42 into 38 at
event127; Int propagation to rows38/8; FreshUse into second-use row56;
replay into row6; row6≤Bool and the resulting Int≤Bool dispatches. All three
traces hash to
`3d8e9aab2c3339efd6ab22059284919e6863bfc057a0201fa0a9e44175df744d`.
The exact aliased-source bytes and exit1 diagnostic receipt also match.

The reviewer performed no write, build, inference run, Git operation or
child delegation. The producer's initial private Cargo-layout failure
(exit101, 0.018s) and repaired build (exit0, 22.065s) remain separate receipts.
The final fresh observer completed in 0.439s with one conflict, seven Calls,
1,404 events, no timeout and no observation cutoff. Observer exit0 is not
compiler acceptance; the unchanged CLI exits1 on this source.

## Integration boundary

The exact rejecting-input observation closes the earlier different-source
trace gap. The source-to-native interpretation and original signed
qualification remain unproved; `same_hir=true` only says that the candidate
retains the HIR supplied to this observer. The private patch is stored as a
reproduction artifact, not applied to production sources. Root stages the
five reviewed paths and this independent receipt explicitly. Raw traces,
compiler output and build products stay outside Git.

The saved unified patch intentionally retains its single-space empty
context-line marker. Whitespace validation keeps that patch byte-exact and
disables only `blank-at-eol` for that one data file; all other packet paths
pass ordinary `git diff --check`. No repository whitespace policy changes.
