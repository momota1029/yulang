# NATIVE-WITNESS-VALIDATION/r10 outcome

Disposition: **CLOSED_INCOMPLETE**. The conditional Lean theorem artifact is checked and accepted; the required Rust witness execution failed. R9 remains CLOSED_INCOMPLETE. No source/native, parent or production gate closes.

## Frozen outputs

- Contract SHA-256: `280fb2e5c37c18e55ae139a449994791605fd20a83442a88b6a91676f5bc9e65`.
- Input manifest SHA-256: `36e54c93c486fb15ba1a01af15104216031335f5bd6c39d6d62c624e1513e9bd` (89 pins, 69 unique paths).
- Rust source remains frozen at R9 `candidate_scheme.rs`, SHA-256 `9701321450cda1500a7aa77c0417bcec4a502e006b3c080591a82b7831e9e4bb`.
- Lean revision 2 SHA-256: `5e44687e7d59f1ccac2da6361befe66bc7a19ed3744d0dc4bc029ea9c48e61f6`.
- Proof handoff SHA-256: `4f4523ee1ba2b2f1919c8b4cf6dd877410705d77efa7f60f35523799aadb6b4f`.
- Independent review: `tasks/agent-loop/inbox/native-witness-validation-r10-review.md`.

## Check results

The one authorized Cargo attempt compiled and executed the focused fixture, then failed: exit 101, 42.3974s, CPU peak sample 41.09s, process-group RSS peak 1,866,809,344 bytes against 2,147,483,648, CPU affinity 0. Exactly 0 passed / 1 failed; `replay_constructor_lineage_observes_rejected_cross_route_authentication` panicked at `candidate_scheme.rs:8019` because `session.execute()` returned `ReceiptMismatch`. Mutation/restoration and rejection assertions were not reached. The boundary was not hit. This is a blocking falsifier for the packet’s Rust success predicate. No retry is authorized.

The first Lean attempt exited 1 in 2.9915s, RSS 609,067,008 bytes, because `.sink` remained ambiguous at line 208; three downstream audits showed `[propext, sorryAx]`. One pre-authorized local repair qualified existing constructors as `Effect.sink` while preserving all seven theorem declarations, assumptions, represented prefixes, `WriteAll` and exact `extract`.

After fresh independent review of revision 2, Lean attempt 2 exited 0 in 2.8162s, RSS 606,412,800 bytes. All seven complete types and transitive audits printed. `effect_frame`, `effect_keeps_replay_undo`, `effects_frame`, and `every_prefix_frame` have no axioms. `callback_frame`, `observed_capacity_frame`, and `native_frame_conditional` have `[propext]`. There is no `sorryAx` or project axiom in the successful result.

All 12 exact argv/stdout/stderr/resources log hashes were independently matched by the reviewer. Cargo logs: argv `1d725e88295d77a1b1e09e1239c5e8b5757213c1280ffaa0b522b86297f75323`, stdout `ebcbe9f7785ee57246f8b823e3a1a947e7753d8e8d9fafa5275ea277e7e925b4`, stderr `e17f45a7937f532b09d69333dfae19034860877ba641915b063410326431e0f1`, resources `df8a65c59a99b58be11b5db71efa67a1701c7e7dec33934eeb03d6f357b0e7af`.

## Review and remaining gates

Review verdict: accept the conditional Lean mathematics; reject Rust witness success. The Rust failure shows only that `session.execute()` returned `ReceiptMismatch`; its deeper cause is not established. Closing it requires a new packet for diagnosis at the receipt owner, preserving the exact fixture/assertions, independent review of frozen repair bytes, and a fresh successful execution.

`extract`, standard I/O realization, native/source correspondence, `NativeCorrespondence`, original `YulangClosure.SourceProblem.InferenceSoundness`, effect hygiene and production remain OPEN. No promotion follows from this conditional Lean check.

## Receipts

- Proof worker stopped at 10:57:45 UTC after revision 2 freeze; spent 241/300 seconds; repair round consumed; no checks run by proof lane.
- Reviewer authenticated the 89 pins and stopped read-only before its conservative assignment cutoff; no edits, checks, Git or descendants.
- Primary’s single Cargo and two Lean attempts stayed within their specific resource limits. No source was modified in R10.
