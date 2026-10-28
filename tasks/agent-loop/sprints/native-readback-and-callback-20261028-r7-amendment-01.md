# NATIVE-READBACK-AND-CALLBACK/r7 amendment 01

Base contract SHA-256: `35b3b0b23eeeb842acddc47ce4685bb8bd1ad6152825c9d1cbba4ba6bce0840a`.
Superseded proof-input manifest: `tasks/agent-loop/sprints/native-readback-and-callback-20261028-r7-proof-inputs.json`, SHA-256 `72cd5bb14ddc4f203d0f4ce8a311b0b4204376a9e1139add990105530184e200`.
New immutable manifest: `tasks/agent-loop/sprints/native-readback-and-callback-20261028-r7-proof-inputs-r2.json`.

## Reason and bounded authority

The proof producer, while reading only the admitted pinned `lib.rs`, identified callback and support owners outside the original 15-file immutable input. The exact-prefix callback obligation cannot use opaque state-preservation assumptions. This amendment adds four read-only source files to a new immutable snapshot. It does not change the parent, semantics, outcome, write lease, total grant, review gate, or check policy. It does not claim the callback read cone is complete.

The additive inputs, authenticated from the admitted `7b3ad7074` source snapshot, are:

```text
crates/yu-solver/src/incoming_sample_trace.rs  b3b10bed1b41b138a83e37346969f946deeac43192ae0e551f8c343fd44f12c5
crates/yu-solver/src/f5c_draft_heap.rs          b973ec0667e6f80de54d9a1de55df112361859982ea2617dae3fe8d34903b1cb
crates/yu-solver/src/term.rs                    d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1
crates/yu-types/src/lib.rs                      fb3d53cdcce6a2d7149508ba0bdc9dad643cfc795fefdb9914afcb461e4aa6d8
```

These cover the call sites found in the pinned `lib.rs`: TLS `sample`/`completed_sample`; `f5c_session_baseline`, matrix getters/checkpoints and `StructuredPairOwner` shape synchronization; `BranchTermArena`/`TermCapacitySnapshot` reads used by sample and ledger preparation; and `ClosedTypeFinalizationSession::f5c_resource_probe`. Read only the exact methods and support operations that determine writes, Results, panics, and argument evaluation on this callback path. The rest of these files is not authorized for unrelated inspection.

## Required acknowledgment and stop boundary

Before dependent reads or proof writes, the proof producer must independently hash amendment 01, the r2 manifest, and all 19 files in the new immutable snapshot. It must acknowledge every hash and confirm the unspent portion of its original 900-second assignment; this amendment renews no time.

The proof must separately retain: local-clone ledger failures before publication; panic during `completed_sample` argument evaluation after publication; callback panic after publication; completed-trace return; and detached matrix-observer mutation/panic/restore prefixes. It must derive projection preservation from the pinned source bodies, not assume it. If a newly discovered owner or source path is outside the 19 pins, an external write or exit is unresolved, or the remaining grant is insufficient, stop at that first boundary and report it. No automatic transitive path permission is granted.

The Rust rev-1 artifact remains frozen and unchanged. No checks, builds, Cargo, tests, Lean/Lake, formatting, descendants, or additional reviewers are authorized before the unchanged fresh source-first review accepts both frozen artifacts. The original parent, source/native correspondence, and production gates remain OPEN.
