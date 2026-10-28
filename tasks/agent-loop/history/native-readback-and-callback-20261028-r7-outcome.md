# NATIVE-READBACK-AND-CALLBACK/r7 outcome — CLOSED_INCOMPLETE

**Status: CLOSED_INCOMPLETE / REJECTED.** The independent reviewer rejected the frozen package. R7 checks and revisions remain unauthorized. The broader `SourceProblem.InferenceSoundness`, separate `NativeCorrespondence`, effect-hygiene, and production gates remain OPEN. This is a dependency obstruction, not a semantic counterexample.

## Authority and inputs

- Contract: `tasks/agent-loop/sprints/native-readback-and-callback-20261028-r7.md`, SHA-256 `35b3b0b23eeeb842acddc47ce4685bb8bd1ad6152825c9d1cbba4ba6bce0840a`.
- Amendment 01: `tasks/agent-loop/sprints/native-readback-and-callback-20261028-r7-amendment-01.md`, SHA-256 `ad7c7c365cfc6e559df2ec7444c0d851073d40e85db6bfaeeab1cfe3a8bcbef8`.
- Original proof manifest: `tasks/agent-loop/sprints/native-readback-and-callback-20261028-r7-proof-inputs.json`, SHA-256 `72cd5bb14ddc4f203d0f4ce8a311b0b4204376a9e1139add990105530184e200`.
- Amended proof manifest: `tasks/agent-loop/sprints/native-readback-and-callback-20261028-r7-proof-inputs-r2.json`, SHA-256 `e49700a9c8e446633de567c3cafe6ce6eb71d77ca42a393b0c6164c5b93d1aec`; all 19 input hashes matched at amendment ACK and independent review.
- Baseline source snapshot: clean `7b3ad7074` with the three R6 provisional Rust repair files; R7 did not promote R6 evidence.

## Frozen outputs

| Artifact | SHA-256 | Disposition |
|---|---|---|
| Isolated `candidate_scheme.rs` | `c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d` | Source-only candidate |
| Isolated `candidate_context.rs` | `19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec` | Source-only candidate |
| Isolated `candidate_extrusion.rs` | `2fa4cdf965785fc43ff9792af36c1dd86a01d50cf863229de2ddb721878d2477` | Source-only candidate |
| Rust handoff | `d17d9992854beade042b12653393d6838ca073c617220ac7103f164048d2206e` | Frozen revision 1 |
| Required `NativeResourceCallbackR7.lean` | **ABSENT** | No theorem, type, proof term or axiom audit |
| Proof obstruction handoff | `882671cc4df8241d33e423e4570154b12a1797b9a6e9880e622fc0579d6e11ea` | Frozen revision 1 |
| Independent review receipt | `41a934ebfc622d0b9bfed902e501b99722940385d54548b6b2ac00818c42f2a5` | REJECT, revision 1 |

The candidate Rust helpers now convert all eight row/atom and value/effect lanes to their concrete vector element type and reconstruct complete endpoints on readback/removal. The static review found no blocking or major defect in that bounded repair and found the observer/falsifiers and restore-before-assert ordering retained. This does not establish compilation, fixture execution, runtime all-lane coverage, source/native correspondence, the parent theorem, or production readiness.

## Review and rejection

Reviewer: `/root/native_readback_callback_r7_review`, `compiler_referee`; requested Sol/medium, observed model/effort UNKNOWN. Review ACK was 2026-10-28 10:01:36 UTC; final authentication and STOP at 10:03:36 UTC, within its 600-second grant. Exact findings and source receipts are preserved in the review file.

1. **BLOCKING:** the required Lean callback artifact is absent. No theorem, type, proof or axiom audit exists; the obstruction handoff cannot satisfy R7's proof deliverable.
2. **Major:** authenticated source reaches `BufWriter<File>::write_all` through `f5c_session_baseline -> record -> Sink::write_words`. The sidecar buffer/file effects, error/checksum/count updates and panic prefixes are outside R7's admitted callback frame. Amendment 01 explicitly requires stopping at unresolved external writes/exits. This is a dependency obstruction, not evidence that projection preservation is false.
3. **Rust source artifact:** no blocking/major static issue found. Reviewer did not compile or run it. No partial Cargo authorization is implied.

The selector's sprint-end recommendation is to keep R7 closed, then separately admit an external-effect frame and a limited verification packet using the frozen Rust witness. A future proof must represent Sink checksum/failed/count, buffer and external file trace, excluded-interval-before-baseline ordering, and every relevant error/panic prefix. It cannot assume I/O preserves the launch-evidence projection. Any conditional frame and remaining stdlib boundary must be explicit.

## Execution, deviations, and records

No R7 Cargo, tests, Lean/Lake, build, formatter, or compiler checks ran. Rejection permits no such checks. No R7 source revisions ran.

- Rust producer disclosed one accidental read-only `git diff`; there was no Git mutation. Active duration, CPU/RSS and exact runtime launch time are UNKNOWN.
- Proof producer stopped before writing Lean. It disclosed reading the full pinned `incoming_sample_trace.rs`, which printed unrelated helpers; no unpinned owner body was read. Active duration, CPU/RSS and exact grant remainder are UNKNOWN.
- Reviewer printed the entire pinned `incoming_sample_trace.rs`; unrelated helpers were not used as evidence. No unpinned std I/O body, Git, checks, scratch, or writes were used. CPU/RSS and exact active compute time are UNKNOWN.
- Primary's dispatched amendment message contained a one-character SHA transcription error; the actual amendment and `current.json` hashes matched, and the reviewer paused until Luna supplied the exact hash. Primary corrected the frozen extrusion output lease from the R6 input hash to the R7 rev1 output hash before review continued.
- `python3 tools/agent_sprint.py check` passed for closeout state. This is static record validation, not independent review or execution evidence.

No source/native correspondence or original parent claim closes. Unknown/quarantined identities and paths remain unchanged.
