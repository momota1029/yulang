# NATIVE-EXTERNAL-EFFECT-FRAME/r8 outcome

Disposition: **CLOSED_INCOMPLETE / REJECTED**. The conditional frame candidate and frozen Rust witness did not pass their contract-authorized checks. No retry, repair, or promotion is authorized by R8.

## Original obligation and scope

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness` in `notes/theory/lean/YulangClosure/Contracts.lean`:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The full supported source domain, original quantifiers, shared witness, immutable-birth qualification, and annotation-effect hygiene policy remain fixed. `NativeCorrespondence`, source correspondence, the parent theorem, and production remain OPEN. R7 stays CLOSED_INCOMPLETE / REJECTED.

R8 contract SHA-256 `125f46e39e973d67f7831355cfe9bac1df1c583788b6f03601f9d3d973a72740`; input manifest SHA-256 `076b26e9fd35fb60cdc3ce4ca0cab926a424ca3b64cd22aa45b28ae49ecda577`. All 38 manifest inputs matched at admission, proof intake, and independent review.

## Proof lane

Proof worker `/root/native_external_effect_frame_r8_proof`, registered `lean_prover`, requested Sol/high; observed model/effort UNKNOWN. Exact pre-body authentication completed at 10:11:00 UTC. Active work began 10:10:52 UTC and writes stopped 10:21:43 UTC; observed wall interval 651.72 seconds, within the 700-second grant. Only the two leased outputs were written; no source bodies outside the immutable proof snapshot and frozen R7 records were read. No compiler, Lean/Lake, Cargo, tests, Git, formatting, scratch, or descendants were run by the proof worker.

- Lean candidate: `isolated/native-external-effect-frame-r8/notes/theory/lean/YulangClosure/NativeExternalEffectFrameR8.lean`, SHA-256 `0a89a8090650a985c4dd277a4c3c6a2398039ddd7987a2460938b88e0a07a3cc`.
- Proof handoff: `tasks/agent-loop/inbox/native-external-effect-frame-r8-proof.md`, SHA-256 `50665ee827876d9a6cc020d8df863b5411e0b7ef3cc76d8c3433a118edc2384f`.
- Seven conditional theorem declarations were constructed. The handoff correctly marked all theorem checks and axiom audits NOT_RUN. The model retains partial writer buffer/file progress, Sink checksum/failed/count, excluded flush ordering, publication and callback/TRACE/TLS prefixes, Matrix Drop/RELEASE/unwind/secondary-abort prefixes. Native application requires an explicit `extract` premise covering every reached native intermediate state as an exact full-view prefix. No source/native bridge is supplied; external I/O realization, coherent Sink snapshots, native encoding/configuration/overflow and destructor order remain open.

The independent check later failed; the candidate is not a checked theorem. See blockers below and retained logs.

## Frozen Rust witness

The Rust/check snapshot was derived from clean baseline `7b3ad7074` with only the three frozen R7 overlays:

```text
candidate_scheme.rs    c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d
candidate_context.rs   19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec
candidate_extrusion.rs 2fa4cdf965785fc43ff9792af36c1dd86a01d50cf863229de2ddb721878d2477
```

The separate 38-pin R8 manifest covered these exact files and proof/R7 records. No Rust source was edited in R8. Static review confirmed the bounded lane helpers reconstruct concrete element types while preserving owner, lane, and polarity; this is not runtime evidence.

## Independent review

Fresh reviewer `/root/native_external_effect_frame_r8_review`, role `compiler_referee`, requested Sol/medium; observed model/effort, CPU/RSS, and active compute UNKNOWN. ACK/start 10:23:19 UTC; check-only acceptance at 10:25:42 UTC; final retained-log/hash review and STOP at 10:28:32 UTC, within the 400-second grant. The reviewer performed read/hash/search only. One failed `python` lookup exited 127; all authentication was completed with `python3` before source-body reads. No Git, builds, tests, Lean/Cargo, scratch, edits, or descendants occurred in the review lane.

Review receipt: `tasks/agent-loop/inbox/native-external-effect-frame-r8-review.md` (primary-persisted because the reviewer role remained read-only). Initial source-first review accepted only the two exact bounded checks. Final verdict: **REJECT / CLOSED_INCOMPLETE** after both failures. The reviewer independently matched all 38 pins, rechecked the proof artifacts and three Rust overlays, and independently matched all eight retained log hashes.

## Contract-authorized checks and retained evidence

Only after source-first acceptance, Luna ran the two exact checks sequentially, each once, with no retry:

1. Focused Cargo test, Cargo 1.95.0 / rustc 1.95.0; exit 101, 76.4267 seconds, one CPU affinity (CPU 0), max RSS 1,156,504 KiB, no timeout. E0425 at `candidate_scheme.rs:8247`: `emission_cases` is declared at `:7734` in another test and consumed at `:7885`. The requested test binary did not compile and the focused test never executed.
2. Pinned direct Lean check, Lake version reports Lean 4.35.0; Lean 4.35.0; exit 1, 3.2235 seconds, one CPU affinity (CPU 0), max RSS 487,724 KiB, no timeout. Parser/elaboration errors occur at lines 148, 180, 188, 206, 292, 332, 365, and 385, including reserved identifiers `scoped` and `partial`; foundational frame obligations fail at lines 402 and 406.

Retained Lean `#print axioms` output reports:

| Declaration | Axioms |
|---|---|
| `effect_frame` | `[sorryAx]` |
| `effect_keeps_replay_undo` | `[sorryAx]` |
| `effects_frame` | `[sorryAx]` |
| `every_prefix_frame` | `[sorryAx]` |
| `callback_frame` | `[propext, sorryAx]` |
| `observed_capacity_frame` | `[propext, sorryAx]` |
| `native_frame_conditional` | `[propext, sorryAx]` |

These arose during failed elaboration/recovery and establish no accepted theorem. The Rust fixture and Lean candidate both need separately authorized repair, fresh freeze/review, and new checks. R8 grants no such revision.

Eight retained logs (independently hash-matched by reviewer):

```text
isolated/native-external-effect-frame-r8/logs/cargo.argv           332106c2ce0220e8168412bc8a1b374059a25824df746afb2a2182511b266dfe
isolated/native-external-effect-frame-r8/logs/cargo.stdout         e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
isolated/native-external-effect-frame-r8/logs/cargo.stderr         b54b6258943bca7ee5a26cff742d1286034df84c475627b1f081afd65ab6859e
isolated/native-external-effect-frame-r8/logs/cargo.resources.json f8e4499b2ac6459ade73689cc937ea9099ddb2f1a04429d6d7aef4da37a890f8
isolated/native-external-effect-frame-r8/logs/lean.argv            e9b54e82969a2071748b7cd248f5e06fc732571f27f533d76babe6b4867d581f
isolated/native-external-effect-frame-r8/logs/lean.stdout          0b5f13235b7c95719ce80a7ce209ceed08882e4d0236f78f86538cde3dc9c689
isolated/native-external-effect-frame-r8/logs/lean.stderr          e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
isolated/native-external-effect-frame-r8/logs/lean.resources.json  ac7f291cec6a652e6e46804c689396a8031b96ec578abcf6257f3f80c2454ba4
```

## Final boundary

The candidate's conditional representation and bounded static Rust source observations remain useful research evidence only. The `extract` premise itself remains an unproved full-prefix source simulation obligation. The standard-library I/O relation and concrete native bridge are unresolved. No test passed, no Lean theorem checked, no axiom-clean proof accepted, and no parent or production obligation closed.
