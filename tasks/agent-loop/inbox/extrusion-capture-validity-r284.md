# R284 capture-complete invariant — frozen producer handoff

Assignment: `/root/sol_r284_capture_validity`, revision 1. Producer-only,
kernel-checked candidate and counterexample; independent review **NOT RUN**.
Parent: unchanged `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`, contract SHA-256
`4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf`.
R284 contract SHA-256 `b603f920183eed952cfa4df176f81a5026736c4295ecc0bece1b0486c75b8741`.
Original source authority is `notes/design/2026-10-11-yulang-inference-top-level-principles.md`
§§1–3, SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
The R70 proof handoff SHA-256 is
`25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db`.
This result concerns only the abstract Lean `OriginalExtrusionWork` model, not
the accepted source language or Rust implementation.

## Dependency and artifact bytes

The exact 16-input R283-R2 manifest SHA-256 is
`1a6f485ba1e48dc0b351d644d32803a70cbe485aa5793538ab811cc732b409e5`;
all 16 listed inputs matched their hashes before construction. The accepted
R283-R2 review receipt SHA-256 is
`431b907c16dcbd8958bf319c2e7140f81e577418d071cf1e45fdab041c380c0b`.
The governing `OriginalExtrusionWork.lean` SHA-256 is
`c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58`;
the frozen R283 candidate SHA-256 is
`31c83006c8d9b411b00d045fd16c9e5875e8a73d5baead989c7a55315f3a3f10`.
New `notes/theory/lean/YulangClosure/OriginalExtrusionCaptureValidityR284.lean`
SHA-256: `6842d0af28691e18ea6c50f250ff08f14205c5cb45ced3d0c58e07178e30f49c`.
This handoff is the only other authored path. Generated `.lake/build` outputs
are within the exclusive cache lease; the checker created and removed its own
temporary `/tmp/yulang-lean-audit-*` program. No other scratch files remain.

## Exact invariant and result

In namespace `YulangClosure.OriginalExtrusionCaptureValidityR284`, with
`S = OriginalExtrusionWork.State`, `C = OriginalExtrusionWork.Capture`,
`K = OriginalExtrusionWork.CopyKey`, `W = OriginalExtrusionWork.Work`,
`R = OriginalExtrusionRowValidityR283.resultState`, and
`RV = OriginalExtrusionRowValidityR283.RowsValid`:

```lean
CaptureSourceValid (s : S) (source : Nat) :=
  source < s.effects.length ∧ s.qe source < s.effects.length
CapturesValid (s : S) :=
  ∀ id, ∀ incidence ∈ s.captures id,
    CaptureSourceValid s incidence.source
CaptureComplete (s : S) := RV s ∧ CapturesValid s
StepPreservesCaptureComplete :=
  ∀ (funds : OriginalExtrusionWork.Funding) (s : S),
    CaptureComplete s → CaptureComplete (R (OriginalExtrusionWork.step funds s))
```

`incomingJobs` reads `s.captures id` when visiting a positive Effect row and
canonicalizes each incidence source with `s.qe`. Both the raw source and its
kind-separated Effect representative must be in the Effect vector. The clause
quantifies over *all* capture indices, including indices not yet allocated:
`State.allocate` can expose a latent capture list at the newly allocated index
for an arbitrary state. This avoids a reachability premise; it is stronger than
checking only the incidence lists consumed immediately. No analogous Value
capture field exists in this model. `RowsValid` already checks canonical maps
of currently published rows, but its omission of `captures` admitted R283's
row-99 counterexample.

Checked results: `capture_complete_rows` implies `RV`; `capture_gap_excluded`
rejects R283 `captureGap` for every caller; `computed_rowInput_capture_complete`
establishes initialization for the existing computed row input for every caller.
Allocation, canonical-map and queue frame lemmas establish local facts. The
candidate is **not preserved** by the actual `step`: `viewTailGap` has two Value
rows, one Effect row, empty captures, a published allowance view 7 with tail 99,
and a Work Visit of that allowance. It satisfies `CaptureComplete`.
`step funded viewTailGap` returns `.next`, queues a Visit of Effect row 99,
and retains an Effect vector of length 1. The resulting Work violates `RV` and
therefore `CaptureComplete`. The kernel proves
`¬ StepPreservesCaptureComplete` with the original arbitrary-Funding,
every-satisfying-State quantifiers unchanged. This is an exact falsifier of
the R284 candidate predicate, not a falsifier of R70 or of any production
execution. A separate view-tail validity/closure condition is the first
visible missing storage condition.

## Complete theorem types and axiom audit

All names in the following table are fully qualified by
`YulangClosure.OriginalExtrusionCaptureValidityR284.`. The abbreviations above
expand to the indicated fully qualified types. `CC = CaptureComplete`,
`CS = CaptureSourceValid`, `CV = CapturesValid`, `KV =
OriginalExtrusionRowValidityR283.KeyValid`, `CG =
OriginalExtrusionRowValidityR283.captureGap`, `RI =
OriginalExtrusionWork.Computed.rowInput`, `V = viewTailGap`, `F =
OriginalExtrusionWork.funded`, `T f s = OriginalExtrusionWork.step f s`,
`E = OriginalExtrusionWork.Endpoint`, `P = NativeMergeExpansion.Polarity`, and
`Req = NativeValueStructure.Request`.

| Theorem | Complete type, using the explicit abbreviations | `#print axioms` |
| --- | --- | --- |
| `capture_complete_rows` | `∀ (s : S), CC s → RV s` | `propext` |
| `capture_complete_sources` | `∀ (s : S), CC s → ∀ (id : Nat) (incidence : C), incidence ∈ s.captures id → CS s incidence.source` | `propext` |
| `capture_source_valid_of_same_effects_qe` | `∀ (s t : S) (source : Nat), t.effects = s.effects → t.qe source = s.qe source → CS s source → CS t source` | none |
| `capture_source_valid_canonical_change` | `∀ (s t : S) (source : Nat), t.effects = s.effects → source < s.effects.length → t.qe source < s.effects.length → CS t source` | none |
| `capture_source_valid_allocate` | `∀ (s : S) (key : K) (source : Nat), CS s source → CS (s.allocate key) source` | `propext`, `Quot.sound` |
| `captures_valid_allocate` | `∀ (s : S) (key : K), CV s → CV (s.allocate key)` | `propext`, `Quot.sound` |
| `captures_valid_pushed` | `∀ (s : S) (pending : Bool) (items : List W), CV s → CV (OriginalExtrusionWork.pushed pending items s)` | `propext`, `Quot.sound` |
| `incoming_child_valid` | `∀ (s : S) (key : K) (incidence : C), CS s incidence.source → KV s ⟨s.canonical (E.effect (.row incidence.source)), P.positive, key.target⟩` | `propext` |
| `incoming_visit_queued` | `∀ (s : S) (id tail : Nat) (incidence : C) (target : Nat), incidence ∈ s.captures id → W.visit ⟨s.canonical (E.effect (.row incidence.source)), P.positive, target⟩ ∈ OriginalExtrusionWork.incomingJobs s ⟨E.effect (.row id), P.positive, target⟩ (E.effect (.row tail))` | `propext`, `Quot.sound` |
| `incoming_visit_queued_valid` | `∀ (s : S) (id : Nat) (incidence : C) (target : Nat), CV s → incidence ∈ s.captures id → KV s ⟨s.canonical (E.effect (.row incidence.source)), P.positive, target⟩` | `propext` |
| `capture_gap_excluded` | `∀ (caller : Req), ¬ CC (CG caller)` | `propext` |
| `computed_rowInput_capture_complete` | `∀ (caller : Req), CC (RI caller)` | `propext`, `Quot.sound` |
| `view_tail_gap_capture_complete` | `CC V` | `propext`, `Quot.sound` |
| `view_tail_gap_pending_bad` | `W.visit ⟨E.effect (.row 99), P.positive, 0⟩ ∈ (R (T F V)).work` | `propext` |
| `view_tail_gap_next` | `T F V = .next (R (T F V))` | `propext` |
| `view_tail_gap_effect_count` | `(R (T F V)).effects.length = 1` | `propext` |
| `view_tail_gap_step_invalid` | `¬ CC (R (T F V))` | `propext` |
| `step_preserves_capture_complete_counterexample` | `¬ StepPreservesCaptureComplete` | `propext`, `Quot.sound` |

The printed helper types and axiom results matched these 18 entries. No
`Classical.choice`, project axiom or `sorryAx` was reported. The two frame
theorems with no axiom dependencies are explicitly marked `none`. These are
kernel/checker acceptance facts, not independent mathematical review.

## Checks, failure evidence and boundaries

Pinned native Lake path:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
`lake --version` returned Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, exit 0;
`lake env lean --version` returned Lean `4.35.0` commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, exit 0.
From `notes/theory/lean`, `lake build
+YulangClosure.OriginalExtrusionCaptureValidityR284` built 14 jobs, exit 0;
`lake env lean -j1 -M1024
YulangClosure/OriginalExtrusionCaptureValidityR284.lean` exited 0.
From repository root, `python3
.agents/skills/yulang-lean-proofs/scripts/check_lean.py --module
YulangClosure.OriginalExtrusionCaptureValidityR284` with all 18 fully qualified
`--theorem` arguments exited 0; its internal focused build and printed-type /
axiom audit both exited 0. `rg` for `sorry|admit|axiom|unsafe|skipKernelTC` in
the new module returned no matches (exit 1). The first focused build failed on
an uneliminated `key.endpoint` match in the allocation frame and an unsimplified
step-result length; a later build failed on the pushed-state match. Case
splitting and exact length lemmas repaired both. Those were elaboration/proof
failures, not counterexamples. No broad build/test, Rust/Cargo/probe, model edit,
Git operation, external contact or checker bypass occurred.

The decisive counterexample uses `Work.visit` on an Effect allowance and the
`.next` projection. No preservation result is claimed for the other seven Work
constructors, other Visit branches, `.external`, `.failed`, partial publication,
arbitrary Funding success/failure branches, or finite `runPrefix`; universal
preservation is already refuted. The checked computed initialization cannot be
inducted to the three-step computed row prefix through this false invariant.
On the unchanged R70 edge this supplies a necessary storage condition and a
new failure of a proposed abstract entry-validity invariant; it discharges no
R70 entry-to-return premise. The next owner must derive a view-tail validity
condition, prove it with all actual transitions including failure states, and
then establish Rust `candidate_source`/`candidate_intrusion` initialization
and mutation correspondence. R70, Simple-sub A/B, Parent, source/native
correspondence and production authority remain OPEN. No source-qualified code
slice follows from this model-only example.

Resource use: bounded focused Lean processes only; exact CPU/RSS unknown.
No descendants. **STOP / WRITES_STOPPED** after this handoff and final read-only
hash check; cache, module and handoff leases return to Luna for reconciliation
and independent review. No carryover requested.
