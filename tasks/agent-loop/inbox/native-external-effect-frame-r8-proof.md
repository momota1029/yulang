# NATIVE-EXTERNAL-EFFECT-FRAME/r8 proof handoff

Disposition: **CONSTRUCTED, UNCHECKED, CONDITIONAL; writes stopped.** No kernel acceptance, axiom result, source correspondence, independent acceptance, parent closure or production promotion is claimed.

## Authentication and authority

Worker `/root/native_external_effect_frame_r8_proof`, registered Lean leaf, requested Sol/high; observed model/effort UNKNOWN. Grant 700 seconds, no renewal. Start observed `2026-10-28 10:10:52 UTC`; complete pre-body hash ACK `10:11:00 UTC`. Contract SHA-256 `125f46e39e973d67f7831355cfe9bac1df1c583788b6f03601f9d3d973a72740`; complete manifest SHA-256 `076b26e9fd35fb60cdc3ce4ca0cab926a424ca3b64cd22aa45b28ae49ecda577`. Independently hashed all 38 entries before source-body reads: 19 proof + 7 R7 records + 12 Rust, all exact MATCH, zero missing/mismatches. The hash command exited 0. Proof manifest SHA-256 `e49700a9c8e446633de567c3cafe6ce6eb71d77ca42a393b0c6164c5b93d1aec` matched both itself and the pinned R7 record.

Source bodies were read only from `isolated/native-readback-and-callback-r7-proof-input-r2/` and the frozen R7 records. The R8 mutable Rust snapshot was hashed only; no Rust source bodies there were read. Operational rules/skill/contract were also read. No new unpinned source owner was opened. No descendants, shared-status writes, compiler/Rust edits, Git, formatter, installation or scratch outputs.

## Artifact and exact declarations

Only Lean source: `isolated/native-external-effect-frame-r8/notes/theory/lean/YulangClosure/NativeExternalEffectFrameR8.lean`, SHA-256 **`0a89a8090650a985c4dd277a4c3c6a2398039ddd7987a2460938b88e0a07a3cc`** (17,691 bytes). Namespace `YulangClosure.NativeExternalEffectFrameR8`; imports only `Init`. No rejected R6 proof is imported.

Constructed theorem types below use names relative to that namespace; every declaration has an in-file `#print` and `#print axioms` command for the primary's single gated check:

```lean
effect_frame (s : State) (e : Effect) : pi (e.apply s) = pi s

effect_keeps_replay_undo (s : State) (e : Effect) :
  (e.apply s).observed.replayUndoCapacity = s.observed.replayUndoCapacity

effects_frame (s : State) (es : List Effect) :
  pi (applyEffects s es) = pi s

every_prefix_frame (s : State) (es : List Effect) (n : Nat) :
  pi (applyEffects s (es.take n)) = pi s

callback_frame (s : State) (io : WriteAll) (p : CallbackPlan) :
  pi (applyEffects s (callback io p).effects) = pi s

observed_capacity_frame (s : State) (io : WriteAll)
    (changed active : Bool) (p : CallbackPlan) :
  pi (applyEffects s (observeCapacity io changed active p).effects) = pi s

native_frame_conditional {Native : Type} (view : Native → State)
    (reaches : Native → Native → Prop) (start : Native)
    (io : WriteAll) (changed active : Bool) (p : CallbackPlan)
    (extract : ∀ stop, reaches start stop → ∃ n : Nat,
      view stop = applyEffects (view start)
        ((observeCapacity io changed active p).effects.take n)) :
  ∀ stop, reaches start stop → pi (view stop) = pi (view start)
```

These are written types and proof terms, not checker-printed types. All actual theorem diagnostics and complete transitive axiom results are **NOT_RUN**. Source search found no `sorry`, `admit`, project `axiom`, kernel bypass or native-evaluation tactic in the candidate; rg exit 1 means no matches, not a kernel audit.

## Source mapping and represented prefixes

- Pinned `candidate_context.rs:949–992` separates `replay_operations`, `typed_drains` and `processing`; pinned `lib.rs` separates the session worklist/processing from counters, resource ledger, sample flags and observer. `LaunchEvidence` retains operations, frames, worklist and both processing owners as separate images. `Effect.apply` only writes `observed`. This is an explicit source-footprint abstraction; native encoding is unresolved. No opaque I/O premise asserts projection preservation.
- `lib.rs:9253–9265`: physical-change mark is first, before sampling. Only the returned callback `Exit.error` appends the session sample-failed mark; panic and abort do not pass through the Err handler. Sink.failed is a separate field, updated by swallowed write_all Err.
- `lib.rs:10774–10802`: sample TRACE prefixes precede attempt increment; a checked attempt-overflow exit is distinct. The sampled peak uses `route_journal.value_rows.capacity()` through a distinct `routeJournalValueRowsCapacity` input and field. Replay undo capacity is retained separately and has no write constructor. Optional overflow checks and usize limit are explicit plan inputs, without asserting native configuration realization.
- `lib.rs:10821–11446`: prepublication resource preparation can return Err or panic. On success, ledger, counters and sample count publish in source order. Route-lane fold panic, baseline entry/borrow/WalkerLedger mutation/panic, and baseline return follow publication. Local preparation arithmetic and full record images are not proved; their exact native extraction is part of the open premise.
- `f5c_draft_heap.rs:299–319,378–397,540–554`: `Sink` retains nextId, count, checksum, failed, excluded interval/current capacities and bytes, dirty flag and writer. `Writer` retains buffer, cumulative external file trace and per-progress observations. `WriteAll := Writer → Bytes → Reply` receives no launch/session state. Each reply retains any finite sequence of partial buffer replacements and file appends, then normal/error/panic/abort. `Progress.consumed` is cumulative input acceptance, independent of file bytes flushed. A ghost Writer.calls serial permits different replies for otherwise identical requests. This instrumentation is an abstract execution history, not an added Rust field.
- `writeWord` emits partial writer changes before the returned Err failed flag, then wrapping u64 checksum. Err becomes normal loop continuation. Panic/abort retains partial changes without failed/checksum for that word. Eight-word `Words` normalizes native u64 casts. Checked count increment occurs only after all words; count overflow preserves earlier writes and checksum.
- `flushExcluded` writes the excluded-interval record first; only its normal completion publishes interval capacity, interval bytes and dirty=false in order. `record` starts the baseline record only afterward. Panics retain the completed/partial excluded record and every earlier field update. Baseline constants 8, excluded interval 10, Unclassified code 0 come from the pinned source.
- `lib.rs:10992–11009` and `incoming_sample_trace.rs:142–238`: completed-sample argument evaluation is separate from completed TRACE entry, its intermediate mutation prefixes and normal TLS return. Thus argument panic after ledger/counters/sample/baseline publication does not acquire a completed trace. TRACE image lists can represent every mutation before its own panic; milestone 6 occurs only on its normal return.
- `lib.rs:20414–20744`: matrix presence, detachment, mutable detached images, sidecar/WalkerLedger effects, restoration and panic are distinct. On panic, cleanup can emit additional RELEASE records; its partial sidecar state is retained. `F5cMatrixObserver` owns `F5cLiveEventLedger` (`lib.rs:4938`, Drop `:5013`) and structured-pair owners (`f5c_draft_heap.rs:1000–1027`); live-owner release is `:1150–1168`. MatrixPlan.unwind retains these destructor prefixes and owner flag/image mutations. A cleanup panic is an abort boundary; it is never ordinary return or implicit restoration. The primary explicitly confirmed this pinned-owner expansion at `10:13` during this assignment.

## Explicit conditional boundary and omissions

`WriteAll` is deliberately an arbitrary overapproximation. No property of std::io::Write::write_all or BufWriter<File> is asserted: byte conservation, consumption bounds/monotonicity, buffer capacity, exact OS errors and native panic configuration are not proved. The frame theorem works for every reply in that model because external access is typed to Writer; buffer/file writes are retained rather than erased. Standard-library source bodies were not read.

The substantive additional premise is **extract** in `native_frame_conditional`: one fixed io/plan and one complete trace must represent every actual reached state as an ordered prefix, including intermediate local arithmetic/TRACE updates, external partial writes, borrow transitions as observable through the abstraction, matrix detachment, destructor sidecar writes, unwind and secondary panic. Native may be a history-bearing execution state so ghost call serial/progress are defined. The premise also requires coherent successive Sink snapshots across baseline/matrix records, exact current-field images, correct cfg/usize/overflow settings and complete cleanup order. This is a strong unproved source-to-interface/refinement obligation. It does not follow from the model's frame calculation or from Rust tests. The native theorem is conditional only and supplies no nativeResult/callback-exit equivalence theorem.

The plan compiler preserves the represented ordering and every admitted effect prefix. Exact native coverage, each local plan's realizability, trace-image arithmetic, native handle encoding and field/alias separation remain source-correspondence duties. No statement that all arbitrary model plans are native executions is made. No independent source-to-interface bridge is delivered. Abort denotes the last observable prefix before process termination, not a returned Rust value.

Original claim was read in pinned `2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5 and `Contracts.lean:128`; the birth-level correction §§2–6 and annotation-effect policy §1/clarifications remain authoritative. Parent:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

No original source constructor, quantifier, scope or shared witness is removed. The candidate can discharge only a callback-frame premise after extract is established. The first remaining concrete owner is the primary's source/native bridge packet for this callback and external interface; later `clear_diagnostic_scratch` and the original lawful joint source strategy at qualified App/Call-demand extrusion remain open. No concrete SourceProblem/LocalLaws instance, whole-language inference theorem, full native correspondence, effect-hygiene proof or production authority follows.

## Execution and cessation

Pinned files inspected: Lean `leanprover/lean4:v4.35.0`, empty package list, `-j1 -M1024`. By this fixed packet the leaf ran **no Lean/Lake/compiler/check/build/Cargo/test/formatter**; actual tool versions, command exits, goals and axiom output are unavailable. The only executed operations were read/search/hash/date and exact leased file writes; source/hash tools exited 0 except the disclosed no-match rg exit 1. No cache/generated outputs were touched. The primary owns any check after fresh source-first acceptance.

At final source hash `2026-10-28 10:19:55.889724 UTC`, elapsed observed wall time was 543.89 seconds from 10:10:52 (includes tool waiting); this is not active CPU use. Final handoff receipt timestamp is supplied to the primary with its hash. CPU/RSS and exact active compute time UNKNOWN. All writes are stopped before the 700-second deadline (`10:22:32 UTC`, or any earlier primary bound). Only the two leased output paths were changed; no scratch paths exist. No further edits or checks are authorized by this handoff.
