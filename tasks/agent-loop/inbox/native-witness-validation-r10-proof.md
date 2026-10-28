# NATIVE-WITNESS-VALIDATION/r10 proof handoff

Assignment `/root/native_witness_validation_r10_proof`; artifact revision **1**, handoff revision **1**. **CONSTRUCTED, UNCHECKED, CONDITIONAL.** Initial freeze at 2026-10-28T10:55:35.128862+00:00; writes stopped pending the primary's first authorized diagnostic within the original 300s bound. No self-certification.

## Authentication, exact change and ownership

Baseline `7b3ad7074`. Contract `tasks/agent-loop/sprints/native-witness-validation-20261028-r10.md` SHA-256 `280fb2e5c37c18e55ae139a449994791605fd20a83442a88b6a91676f5bc9e65`. Input manifest `tasks/agent-loop/sprints/native-witness-validation-20261028-r10-inputs.json` SHA-256 `36e54c93c486fb15ba1a01af15104216031335f5bd6c39d6b62c624e1513e9bd`. Authenticated **all 89 entries before source/proof/contract body reads**, zero mismatches. Initial R10 bytes and frozen final R9 input both SHA-256 `747150d9627b84830389ff1b088f43b78da64c3b1f432dbc868a7466b51d1ad9`.

Changed only `isolated/native-witness-validation-r10/NativeExternalEffectFrameR8.lean`, revision 1 SHA-256 **`91f5e8bffa32fa67822b917373a4c10d38a73f586b37349b2a49d2189cadfaaa`**, and this exact handoff path. The sole Lean change is at line 208: `[.sink failed]` becomes `[Effect.sink failed]` in `writeWord.failureEffects`. This selects the existing effect constructor; definitions, all seven theorem statements/bodies, interfaces, model state, all assumptions and all represented prefixes are otherwise byte-preserved. No scratch paths. No compiler/Rust/root-import/config/dependency/Git/status edits. The exact fixed Rust input `candidate_scheme.rs` remains SHA-256 `9701321450cda1500a7aa77c0417bcec4a502e006b3c080591a82b7831e9e4bb`.

Direct import remains `Init`. Authenticated dependency environment: `leanprover/lean4:v4.35.0`, `YulangClosure` library, `-j1 -M1024`, no external packages. Immutable toolchain SHA-256 `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; lakefile `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`; manifest `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`. Primary owns all execution, cache/generated outputs and exact logs; this leaf ran no check, build, formatter, Lean, Lake, Cargo or installation.

## Original specification, corrections and parent

Read authenticated immutable `isolated/native-readback-and-callback-r7-proof-input-r2/notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, §§1, 3, 5 (SHA-256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`). §1 quantifies all supported original programs, lawful finite construction histories, actual retained occurrences and original scopes, with one joint evidence strategy. §3 distinguishes original non-let paper sketches from full Yulang coverage; §5 leaves complete source-rule/scope transport open. The referenced original PDF is `/home/momota1029/rust/simple-sub-reference-paper.pdf`, §§3.5.1–3.5.2, Figs. 6–9 and §5; this packet uses the authenticated parent specification and does not claim a fresh PDF reading.

Read corrections: immutable birth-level SCC design §§2–6, SHA-256 `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`; annotation-effect policy §§1–1.1, SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`. Qualification uses paths wholly inside one immutable-birth Value induced graph; cross-level references remain source dependencies. Contravariant annotation grants local subtraction permission without a closed input-effect bound. These policies and accepted features are preserved. Research drafts supply no semantic authority.

Exact parent definition read in immutable `YulangClosure/Contracts.lean:128`, SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`:

```lean
YulangClosure.SourceProblem.InferenceSoundness p =
  ∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
    ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceProblem` and `LocalLaws` are interfaces/obligations, not concrete instances. This repair does not construct a source derivation or shared witness.

## Seven unchanged theorem types and audit status

All declarations are in namespace **`YulangClosure.NativeExternalEffectFrameR8`**. Types below are exact source statements, **not a fresh kernel print**. In-file `#print` and `#print axioms` remain for all seven. Current revision's kernel acceptance and complete transitive axiom audits: **NOT_RUN for all seven**.

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

`WriteAll` remains exactly `Writer → Bytes → Reply`; it receives neither `State` nor launch evidence. `native_frame_conditional` retains precisely the printed `extract` premise above, quantified over every reached native stop, with one fixed `io`, `changed`, `active` and `p`. No hypothesis was strengthened or conclusion weakened.

## Represented and omitted cases; application to parent

Preserved: empty and every finite effect prefix, arbitrary partial writer progress/buffer/file effects, Err swallowing, per-word checksum and count overflow, excluded interval writes, cfg plan choices, attempts overflow, preparation error, publication, baseline, completed-callback argument/TLS boundaries, matrix detach/restore/RELEASE/drop, unwinding and secondary abort. All opaque owner images and caller-supplied intermediate plans/exits remain explicit. Standard-library byte-order/progress correctness, concrete handle encoding, coherent native extraction/cfg realization/destructor order remain open; no full source feature is removed.

The native source footprint remains the authenticated R7 context replay operations/drains/processing (`candidate_context.rs:949–992`), callback/publication and matrix owners (`lib.rs:9253,10774–11446,20414–20744`), sidecar/walker/drop owners (`f5c_draft_heap.rs:299–319,378–397,540–554,1000–1027,1150–1168`) and TLS (`incoming_sample_trace.rs:142–238`), as recorded in the frozen source and R9 handoff. This packet changes only a constructor spelling; it supplies no new correspondence proof.

Conditional application: `effect_frame` → `effects_frame` → `every_prefix_frame`; then `native_frame_conditional` composes exact `extract` with prefix preservation. First remaining premise: establish **the exact `extract` trace for every actual native intermediate state under a single fixed interface/plan**, including partial IO and unwind/drop. Owner: **primary source/native correspondence lane**. `clear_diagnostic_scratch`, seed/enqueue/Running, `NativeCorrespondence`, full source/native correspondence, the original shared-witness parent, effect hygiene and production stay **OPEN**. Conditional mathematics, kernel acceptance, independent review and production authority remain distinct.

## Actual commands, failure evidence and resource/stop receipt

Executed only `pwd`, `cat`, `sed`, `rg`, Python read/hash/authentication and the exact two output writes; all completed command exits 0. Authentication output: `PIN_COUNT 89 BAD []`. No children or nested CLI. No tests or bundled skill checker; the fixed packet prohibits leaf execution. CPU/RSS unmeasured. Requested routing Sol/high; effective model/effort metadata UNKNOWN.

Material prior evidence remains untouched: R9 `logs/lean-1.stdout` SHA-256 `8f5bb3dd27efeae958ccd58cf5eba6179f675347ee3ff0c4dbc4fa15494f4875`, `lean-1.argv` SHA-256 `f5b1eb40f3e9f98de9355192b556f384e248c6f9d51e0be7ea885b3b0c0d5b45`, resources `e7da42cf792fb6e409cf96c29c8c380dd2b9c81baa65646955c63d68090696a0`. Read actual diagnostic: line 208 `lean.invalidDottedIdent`, ambiguous `.sink`; hints include `Effect.sink`. R9 command was `taskset -c 0 lake env lean -j1 -M1024 YulangClosure/NativeExternalEffectFrameR8.lean`, exit 1, wall 3.1599s, sampled peak RSS 606572544 bytes. Retained versions: Lake `5.0.0-src+eb6cafb` (Lean 4.35.0); Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64-unknown-linux-gnu Release. These are **R9 recorded versions/results**, not R10 execution by this leaf.

R9 complete axiom outcomes: `effect_frame`, `effect_keeps_replay_undo`, `effects_frame`, `every_prefix_frame`: no axioms; `callback_frame`, `observed_capacity_frame`, `native_frame_conditional`: `[propext, sorryAx]`. R9 is **CLOSED_INCOMPLETE**. This revision is constructed to repair its elaboration failure; no clean R10 audit is claimed.

Budget accounting: conservative start `2026-10-28 10:53:44 UTC`; freeze `2026-10-28T10:55:35.128862+00:00`; elapsed 111.1s, remaining 188.9s of the original 300s grant, deadline `2026-10-28 10:58:44 UTC`, no renewal. **Revision 1 writes stopped**; waiting for primary diagnostic. Only one directly resulting local elaboration repair is pre-authorized within this original deadline; it must freeze as revision 2 and receive fresh independent review before primary attempt 2. Absent timely diagnostic, stop with no speculative revision. Primary mutual TODO: authenticate/fresh-review this exact hash before attempt 1, retain complete types/axioms/logs, and send only in-scope first diagnostic promptly. Final cessation will be reported by message without changing this frozen handoff unless the authorized repair round occurs.


## Revision 2: authorized diagnostic repair and final cessation

The original revision 1 account above is retained as failure history. Correction: its sole modification was actually **line 215**, `failureEffects`, not line 208. The R9 diagnostic's line 208 points to `.sink called` inside the `partial` segment; I had selected the later unqualified constructor in revision 1. Revision 1 did not resolve that first error.

Primary supplied the actual first R10 Lean diagnostic within this original assignment; I read the retained stdout/argv/resources. R10 attempt 1 on revision 1 exited **1**, wall **2.9915s**, CPU peak sampled **1.25s**, sampled process-group peak RSS **609067008 bytes**. The actual Lean 4.35.0 diagnostic is `208:48 lean.invalidDottedIdent`, ambiguous `.sink` in the `partial` segment. All seven types printed; complete audit results were: first four declarations no axioms; `callback_frame`, `observed_capacity_frame`, `native_frame_conditional` each `[propext, sorryAx]`. This failed attempt is preserved, not relabeled success.

Its actual argv is `taskset -c 0 lake env lean -j1 -M1024 /home/momota1029/rust/yulang/isolated/native-witness-validation-r10/NativeExternalEffectFrameR8.lean`, cwd `/home/momota1029/rust/yulang/isolated/native-witness-frame-repair-r9/notes/theory/lean`; versions recorded by the primary are Lake `5.0.0-src+eb6cafb` (Lean 4.35.0), Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64-unknown-linux-gnu Release. No check was run by this leaf.

Retained R10 failure hashes:

- `isolated/native-witness-validation-r10/logs/lean-1.argv` SHA-256 `42755b03f6b47fb8ea492d2e09476070e9bc74da4065a10e405c53c7c130f5c5`.
- `isolated/native-witness-validation-r10/logs/lean-1.stdout` SHA-256 `d1944c8ee03f2f78f5549a89a6845b87c822a9eb5fc4703b9f044d199a53c7fe`.
- `isolated/native-witness-validation-r10/logs/lean-1.stderr` SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `isolated/native-witness-validation-r10/logs/lean-1.resources.json` SHA-256 `58cfb3d92406f5c6b5b62d369f05c846ff06592bb030aa02e28943e5fc804c15`.

Revision 2 artifact SHA-256 **`5e44687e7d59f1ccac2da6361befe66bc7a19ed3744d0dc4bc029ea9c48e61f6`**. Relative to revision 1, qualified only the seven remaining sink effect construction sites on five lines: `progressRun` line 199, `writeWord` line 208 (`partial`) and line 217 (`summed`), `writeLoop` line 225, and `flushExcluded` line 261 (`cap`, `bytes`, `clean`). Each `.sink` effect constructor becomes `Effect.sink`; the revision 1 `Effect.sink failed` remains. The match pattern `| .sink a =>` has an explicit `Effect` scrutinee and remains unchanged; structure field projections remain unchanged. All effect-list sink constructors are now explicit. No directly resulting proof obligation, theorem statement/body, assumption, state, prefix, `WriteAll` interface or exact `extract` premise changed. The seven full types listed above are unchanged and remain this revision's complete theorem inventory.

Current revision 2 status: **CONSTRUCTED, UNCHECKED, CONDITIONAL; independent review PENDING; primary Lean attempt 2 NOT_RUN by this leaf**. All dependency pins remain the authenticated input set; only the leased R10 Lean artifact and this handoff were written. No scratch/generated/cache writes. All parent/source/native/production gates and their owners recorded above remain OPEN; first concrete premise remains exact `extract` for every native intermediate state under one fixed plan/interface.

Final freeze `2026-10-28T10:57:45.047053+00:00`; elapsed **241.0s**, remaining **59.0s** against conservative start `10:53:44 UTC`, original deadline `10:58:44 UTC`. **FINAL WRITES STOPPED.** The single authorized repair round is consumed. No further change will occur under this assignment. Fresh independent review of this exact revision/hash must accept it before primary Lean attempt 2; retain full types and transitive axiom output. Execution, integration and gate adjudication remain primary-owned.
