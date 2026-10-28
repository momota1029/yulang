# NATIVE-READBACK-AND-CALLBACK/r7 review — revision 1

**Verdict: REJECT.** This receipt was persisted by Luna from the read-only reviewer return. Reviewer: `/root/native_readback_callback_r7_review`, `compiler_referee`, requested Sol/medium, observed model/effort UNKNOWN. Session: `NATIVE-READBACK-AND-CALLBACK-20261028/r7`.

## Findings

1. **BLOCKING — required Lean artifact is absent.** `isolated/native-readback-and-callback-r7/notes/theory/lean/YulangClosure/NativeResourceCallbackR7.lean` is absent. No declaration, theorem type, proof term or axiom audit exists. The contract requires a source-grounded exact callback-prefix frame proving preservation of the launch-evidence projection. The obstruction handoff cannot satisfy that deliverable. Under the unchanged review gate, rejection authorizes no checks or revisions. A separately admitted packet would need to construct the artifact, discharge its dependencies, and obtain fresh review before any conditional check.
2. **Major — callback external-effect correspondence is unresolved.** In the authenticated r2 snapshot, `lib.rs:11424` publishes ledger/counters/sample count; `lib.rs:11437` invokes `f5c_session_baseline` before `completed_sample` at `:10995`. `f5c_draft_heap.rs:378` reaches `record` at `:540`, which flushes an excluded interval and invokes `Sink::write_words`. `Sink` owns `BufWriter<File>` (`:299`); `write_words` calls `write_all` (`:305`), updates failure state on returned error, updates checksum per word, then can panic on checked count overflow. A counter-only prefix model would omit a real buffer/file effect. This confirms a dependency obstruction under amendment 01, not a counterexample to projection preservation and not proof that preservation is impossible. Closure needs an authorized, frozen external-I/O interface and source/model bridge covering normal, error and panic prefixes, including excluded-interval ordering.
3. **Rust artifact — no BLOCKING or major defect found in bounded static review.** Rev1 fixes the R6 lane-helper type cause: replace writes the concrete lane element (`u32`, `ValueEndpointKey`, or `EffectEndpointKey`) and reconstructs the full endpoint; removal reconstructs the enclosing Value/Effect endpoint in all eight arms. Polarity, row/atom guards, owner equality and absent-slot rejection remain. The round trip preserves owner, polarity and valid element. Both methods remain `#[cfg(test)]`; no production behavior changes. The observer and falsifiers remain: invocation/handle begin/return joins; FreshUse source/destination and physical-slot reread; raw transformer content resolution; ordinary fixture; restoration before rejection assertions. This is static evidence only; compilation, fixture execution, runtime all-lane coverage and parent/production acceptance remain unproved.

## Authentication

```text
R7 contract        35b3b0b23eeeb842acddc47ce4685bb8bd1ad6152825c9d1cbba4ba6bce0840a
Amendment 01       ad7c7c365cfc6e559df2ec7444c0d851073d40e85db6bfaeeab1cfe3a8bcbef8
r2 manifest        e49700a9c8e446633de567c3cafe6ce6eb71d77ca42a393b0c6164c5b93d1aec
19 proof inputs    all matched
candidate_scheme   c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d
candidate_context  19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec
candidate_extrusion 2fa4cdf965785fc43ff9792af36c1dd86a01d50cf863229de2ddb721878d2477
Rust handoff       d17d9992854beade042b12653393d6838ca073c617220ac7103f164048d2206e
Proof obstruction  882671cc4df8241d33e423e4570154b12a1797b9a6e9880e622fc0579d6e11ea
```

## Limits and process

No concrete original `InferenceSoundness`, `NativeCorrespondence`, or `LocalLaws` instance is established. Full launch owners remain OPEN. The reviewer did not read unpinned std I/O bodies. The reviewer printed all of pinned `incoming_sample_trace.rs`, including unrelated start/event/finish helpers; those helpers were not used as evidence. Producer-disclosed read-only Git and proof read-scope deviations remain disclosed.

Commands were read/hash/search/diff only. No Git, compiler, Cargo, tests, Lean/Lake, builds, formatting, installation, descendants, scratch, generated outputs, or file writes were performed by the reviewer. CPU/RSS and exact active compute time UNKNOWN. Review ACK: 2026-10-28 10:01:36 UTC. Final authentication/STOP: 10:03:36 UTC, within the 600-second cap. No checks are authorized after REJECT.
