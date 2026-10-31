# R94 bounded outcome — exact-input authority hash mismatch

Sprint: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R94`.
Contract SHA-256: `b00a4ddf0aec31ed0a5253b29afa2d7c980b48f1948139fb760f5cab55d19cde`.
Manifest SHA-256: `e8a15ae3e3f749101cbb38631b7776dd8a36db0c68c59712158db34fe97bc370`.
Baseline: `120db95f8f4ad9505ae245884f3c3ab7e8d18c71`.

## Independent exact-input review

The fresh `compiler_referee` returned **BLOCKING / PRE-EXECUTION GATE FAIL**.
All eleven manifest-pinned inputs match their recorded byte counts and hashes.
The independently reconstructed input is 106,897 bytes and has SHA-256
`8bd62910afba8530f2140bd5b150db0d5fb5281c4651b87a88f78c51dc53d0d7`.
The admitted contract and manifest instead require
`8bd62910afba8530f2140bd5b0db0d5fb5281c4651b87a88f78c51dc53d0d7`, which is
only 62 hexadecimal characters and cannot be a SHA-256 digest. No authorization
to execute Lean was issued.

The reviewer statically found ten distinct declarations in
`YulangClosure.OriginalSource.LogicalOccurrencesR93`, each with an adjacent
`#check @…` / `#print axioms …` pair at assembled lines 1992–2011. The source
namespaces close before subsequent module content; only `import Std` remains.
These facts do not cure the digest mismatch.

Reviewer resource receipt: start `2026-10-31 16:50:31 UTC`, stop
`2026-10-31 16:51:03 UTC`, **32 seconds charged out of 300**. Effective
model/effort UNKNOWN. The read-only `compiler_referee` returned its frozen
report inline; it made no filesystem writes. No Lean, Lake, build, test, scratch,
cache, worktree, environment, or project-copy operation occurred. Lean calls:
**0**.

## Closeout and next gate

R94 closes as `CLOSED_BOUNDED_EXACT_INPUT_HASH_BLOCKED`. The R93 candidate and
all dependencies remain unchanged. This is an authority-record transcription
error by the primary; the exact assembled bytes are pinned by the review above.
Any retry requires a separately admitted corrected contract/manifest and fresh
independent exact-input review. R94's review budget is closed at 32/300 seconds;
R93's unknown reviewer time remains closed and is not reused.

The R93 result remains a statically reviewed, unchecked candidate. Original
A/B, semantic admission/readout, source/native correspondence, effect hygiene,
principality, termination and production remain OPEN. No Rust or compiler
semantics change is authorized by this result.
