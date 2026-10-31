# R85 independent review and primary audit record

## Independent review — PASS for the exact conditional Lean audit

Reviewer: `/root/r85_review` (`compiler_referee`), read-only, no descendants. The source and proof authors were STOPPED before review. No files were written by the reviewer, and no Lean, tests, builds, formatters or Git mutations were run.

Frozen files and hashes were independently checked against the R85 input manifest:

- Source handoff: `06f55710a9cbee24e6171435f7062b938d07afca5f079b5fb369bf7d15fcb8b9`.
- Lean candidate: `a3027fb0c80bc6314be61d39a943be278b6320bc54a9a2b1b88ee14bfce3f1db`.
- Proof handoff: `e9e42530183f0637492b038af361eb9c288c620452ae7f03367c91bd7417aab2`.
- Accepted R84 proof recipe: `8241f3b7ab3a656c15d114a987159fd33c66f04ae48fc3d82dbda0e4972ed17b`.

The reviewer found no static defect in the conditional Lean argument. `Pending` is proved by lifecycle induction without assuming `Root`, `Primitive`, or selector uniqueness. `pending_blocks_R84_primitive` uses the unchanged R84 `Primitive`, obtains Origin membership from its unchanged candidate singleton, and contradicts the completed bit on that same attached receipt. The modeled lists retain all competing Origins except explicit rollback truncation. No desired conclusion is placed in a premise.

**BLOCKING for native correspondence:** the producer attaches a false receipt to `Origin`, then appends a completed clone to a separate vector; the checked-root reader requires the attached receipt itself to be completed. The inspected path therefore cannot supply a checked Internal root. The modeled source lifecycle is explicitly conditional: its initial state empties Origins and its `preserve` step requires exact Origin-list equality. Exhaustive sibling-module mutation/initialization mapping is still unproved.

**MAJOR, unresolved:** R57's state/relation-ID-only Origin selector is broader than R84's occurrence/route selector. Relation interning and separate Origin insertion do not establish global Origin uniqueness by relation ID. No successful native-root counterexample or original A/B counterexample is claimed.

Reviewer verdict permits only an audit of the frozen conditional Lean statements. R85 success, authenticated Rust-to-Native correspondence, the selector implication, original A/B, and production remain OPEN.

## Primary exact-input reconstruction

Luna independently reconstructed the R84 normalized prefix, accepted R84 slot-4 stdin, appended R85 source and query text from the frozen files, and verified every selected module hash and normalization hash in memory. The R84 handoff's embedded old manifest receipt (`e49d8af...`) differs from the R85-pinned current R84 manifest (`fa70cfc...`); the selected source-module pins and accepted stdin still match exactly, as follows:

| Input | Bytes | SHA-256 |
|---|---:|---|
| Normalized prefix | 78,934 | `ee4abd52c66c46bf714ca196be6de1fbb46ee2f2f31e17dd882a9c367b14ab49` |
| Accepted R84 stdin | 103,470 | `93b365ddf908e223558d166efe7f76a1f5c370a5b1c9080716d0fb0ce92b3df0` |
| R85 query suffix | 1,626 | `f55f6aeb5717bb22b7949797db45c6d09f8a5713bf3d547182ed58bc377d8fba` |
| Proposed R85 stdin | 115,845 | `2f001a9673e79313db2b57c456c9e0875d43d3b86d225944e33ee198a10759ac` |

The independent reviewer reproduced the same accepted R84 and proposed R85 byte counts and hashes. The pinned Lean executable SHA-256 is `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.

## Primary authorization — slot 1

Authorized by Luna before execution, committed and pushed in this file. Exact input SHA-256: `2f001a9673e79313db2b57c456c9e0875d43d3b86d225944e33ee198a10759ac` (115,845 bytes). Candidate SHA-256: `a3027fb0c80bc6314be61d39a943be278b6320bc54a9a2b1b88ee14bfce3f1db`. Review verdict: PASS for this exact conditional audit.

Command: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`; cwd `notes/theory/lean`; `LEAN_NUM_THREADS=1`; timeout 120 seconds. The input is reconstructed in memory from the manifest-pinned source slices and supplied to Lean over stdin. No source file, scratch file, target, cache, environment, or worktree is created. Complete stdout/stderr and process metadata will be appended below after the call. One of two R85 invocations is authorized; the second remains separately gated.
