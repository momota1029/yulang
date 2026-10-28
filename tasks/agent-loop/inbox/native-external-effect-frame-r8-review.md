# NATIVE-EXTERNAL-EFFECT-FRAME/r8 independent review

Final verdict: **REJECT / CLOSED_INCOMPLETE**. Initial acceptance authorized only the two exact bounded checks. Their retained results invalidate artifact acceptance; no retry or revision is authorized.

## Findings

**BLOCKING — Lean candidate does not elaborate.**
`isolated/native-external-effect-frame-r8/notes/theory/lean/YulangClosure/NativeExternalEffectFrameR8.lean:148`, `:180`, `:188`, `:206`, `:292`, `:332`, `:365`, `:385` have parser/elaboration errors, including reserved identifiers `scoped` and `partial`. The foundational frame proofs fail at `:402` and `:406`. This violates the contract’s checked conditional-artifact requirement and proof-closure prohibition on `sorryAx`. Minimum closure: separately authorized correction of the owning definitions, fresh frozen review, successful pinned check and complete clean axiom audit. Current failed declarations cannot be promoted.

Actual transitive axiom diagnostics:

| Declaration | Retained axiom result |
|---|---|
| `effect_frame` | `[sorryAx]` |
| `effect_keeps_replay_undo` | `[sorryAx]` |
| `effects_frame` | `[sorryAx]` |
| `every_prefix_frame` | `[sorryAx]` |
| `callback_frame` | `[propext, sorryAx]` |
| `observed_capacity_frame` | `[propext, sorryAx]` |
| `native_frame_conditional` | `[propext, sorryAx]` |

These outputs arise during failed elaboration/recovery; they establish no accepted theorem.

**BLOCKING — frozen Rust fixture cannot compile.**
`isolated/native-external-effect-frame-r8/crates/yu-solver/src/candidate_scheme.rs:8247` references `emission_cases`, which is declared at `:7734` in another test and consumed at `:7885`. Cargo reports E0425 and never executes the requested fixture. This violates the frozen Rust witness-check outcome. Minimum closure: separately authorized repair that constructs the intended retained evidence within the owning fixture, followed by freeze/review/check. No fixture expectation change is justified.

No additional major/minor compiler-correctness finding was established.

## Bounded positive observations and remaining boundary

The source review supports the intended *conditional* frame construction: writer progress precedes swallowed-error/failure/checksum/count updates; excluded flush precedes baseline; publication precedes callback milestones; completed arguments and TLS return are separate; matrix detachment, RELEASE cleanup and secondary abort have distinct representations. The Rust lane helpers repair concrete element reconstruction at its owner, preserving owner, lane and polarity. Those static observations survive the failed checks, without becoming executable evidence.

The `extract` premise at Lean `:434` requires one fixed interface/plan to represent **every** reached native intermediate state as an exact full-view prefix. It entails represented evidence preservation and remains an unproved source simulation obligation. Native encoding, coherent Sink snapshots, cfg/overflow realization, destructor order and external I/O realization remain open. Original `InferenceSoundness`, native correspondence and production remain open; R7 remains rejected/incomplete.

## Authentication

- All 38 manifest pins matched before source reads and at recheck.
- Contract: `125f46e39e973d67f7831355cfe9bac1df1c583788b6f03601f9d3d973a72740`.
- Manifest: `076b26e9fd35fb60cdc3ce4ca0cab926a424ca3b64cd22aa45b28ae49ecda577`.
- Lean artifact: `0a89a8090650a985c4dd277a4c3c6a2398039ddd7987a2460938b88e0a07a3cc`.
- Proof handoff: `50665ee827876d9a6cc020d8df863b5411e0b7ef3cc76d8c3433a118edc2384f`.
- Three frozen overlays remained exact after checks.
- All eight primary-announced retained log hashes matched independently; complete outputs and resources were inspected.

Retained log SHA-256 values:

```text
cargo.argv          332106c2ce0220e8168412bc8a1b374059a25824df746afb2a2182511b266dfe
cargo.stdout        e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
cargo.stderr        b54b6258943bca7ee5a26cff742d1286034df84c475627b1f081afd65ab6859e
cargo.resources.json f8e4499b2ac6459ade73689cc937ea9099ddb2f1a04429d6d7aef4da37a890f8
lean.argv           e9b54e82969a2071748b7cd248f5e06fc732571f27f533d76babe6b4867d581f
lean.stdout         0b5f13235b7c95719ce80a7ce209ceed08882e4d0236f78f86538cde3dc9c689
lean.stderr         e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
lean.resources.json ac7f291cec6a652e6e46804c689396a8031b96ec578abcf6257f3f80c2454ba4
```

Retained checks:

- Cargo 1.95.0 / rustc 1.95.0: exit 101, 76.4267 seconds, one CPU affinity 0, maximum RSS 1,156,504 KiB; no timeout.
- Lean 4.35.0 / matching Lake: exit 1, 3.2235 seconds, one CPU affinity 0, maximum RSS 487,724 KiB; no timeout.

## Reviewer receipt

Reviewer ACK/start: **2026-10-28 10:23:19 UTC**. Initial check-only acceptance: **10:25:42 UTC**. Final retained-log/hash review and STOP: **10:28:32 UTC**, within 400 seconds. Requested role/model: compiler_referee, Sol/medium; observed model/effort and reviewer CPU/RSS/active compute: **UNKNOWN**.

Reviewer performed read/hash/search only: no files edited, Git, builds, tests, Lean/Cargo execution, scratch or descendants. An initial absent `python` lookup exited 127; authentication was completed using `python3` before source-body reads. Receipt returned to primary for persistence under the user’s read-only instruction.
