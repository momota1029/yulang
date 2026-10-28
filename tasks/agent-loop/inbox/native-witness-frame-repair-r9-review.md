# NATIVE-WITNESS-FRAME-REPAIR/r9 review receipt

Verdict: **CLOSED_INCOMPLETE; reject checked-evidence acceptance.**

Reviewer: `/root/native_witness_frame_repair_r9_review`. The reviewer remained read-only: no file writes, Git, checks, or descendants. This receipt is persisted by the primary.

## Authentication and source-first review

The reviewer authenticated contract `d57ddde8ea97eff2f6641370b2d58d34c06c51398d16941b26a8244893e9783a`, manifest `9268a0d7cd0eb3a674ba10fd2ec4dba63a25007c2f32fd513510ce44f47cc544`, all 76 manifest entries, both final outputs, and the proof handoff. For the two initial-output manifest entries that became mutable R9 outputs, it matched initial bytes against the unchanged R8 snapshot copies. All eight retained first-attempt log hashes independently matched the primary's frozen hashes.

Initial source-first review accepted the exact frozen Rust and Lean outputs for their first conditional attempts. Rust repairs the missing binding inside its owning fixture; fixture text, assertions, provenance checks, and mutation/restoration logic remain unchanged. Lean preserves all seven theorem statements, `WriteAll`, `extract`, and the represented partial I/O, callback, and unwind prefixes.

## Blocking findings

1. **Lean elaboration remains incomplete.** At `NativeExternalEffectFrameR8.lean:208`, `.sink` is ambiguous. Lean 4.35.0 exited 1. The audits for `callback_frame`, `observed_capacity_frame`, and `native_frame_conditional` contain `[propext, sorryAx]`; the other four declarations report no axioms. The successful elaboration and clean complete axiom-audit criterion is unmet. Disambiguating the existing effect constructor without changing semantics would need a new packet, independent review, and a check. No repair ownership remains in R9.

2. **The required Rust witness did not execute.** `cargo-1.resources.json` records exit `-15`, `WALL_LIMIT`, and 90.0848 seconds; stdout is empty. Sampled peak process-group RSS was 1,712,734,208 bytes. No successful focused-fixture evidence exists. This misses the success criterion and triggers the resource-boundary stop clause. R9 authorizes no further attempt.

The first review gate accepted the initial frozen outputs, but the retained checks do not satisfy the packet. `extract`, standard-library I/O realization, exact native trace coverage, source/native correspondence, `NativeCorrespondence`, original `SourceProblem.InferenceSoundness`, effect hygiene, and production remain **OPEN**. No R8 result is promoted.
