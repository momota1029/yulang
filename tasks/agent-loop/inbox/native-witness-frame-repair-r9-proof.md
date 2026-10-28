# NATIVE-WITNESS-FRAME-REPAIR/r9 proof handoff

Assignment `/root/native_witness_frame_repair_r9_proof`; handoff revision **1**; candidate revision **1**. Disposition: **CONSTRUCTED, UNCHECKED, CONDITIONAL; initial bytes frozen; writes stopped pending primary first-check diagnostics.** No proof acceptance or self-certification.

## Authority, authentication and receipt

Contract SHA-256 `d57ddde8ea97eff2f6641370b2d58d34c06c51398d16941b26a8244893e9783a`; manifest `tasks/agent-loop/sprints/native-witness-frame-repair-20261028-r9-inputs.json`, SHA-256 `9268a0d7cd0eb3a674ba10fd2ec4dba63a25007c2f32fd513510ce44f47cc544`, baseline `7b3ad7074`. Both match. Before any assigned proof/source body reads, authenticated all 61 assigned proof/governing/record/log manifest entries (41 unique paths), zero missing/mismatch; Python SHA-256 command exit 0. Excluded the 12 R8 Rust lane entries and three R9 Rust entries from assigned proof-input authentication. The mutable R9 Rust source body was never read. Immutable Rust bodies came only from `isolated/native-readback-and-callback-r7-proof-input-r2/`.

Pre-proof-body ACK sent to primary with exact two write leases, no execution/Git/descendants/scratch/cache, all authentication results. Ordering disclosure: the contract body was read alongside startup rules before its hash command; its hash subsequently matched. Proof and source body reads followed authentication and the ACK.

Registered leaf requested Sol/high; observed effective model/effort UNKNOWN. No authors or descendants besides this worker. Finite 600-second grant, no renewal; active origin approximately `2026-10-28 10:35:45 UTC` (first explicit clock sample `10:36:11 UTC`). Initial freeze approximately `10:39 UTC`; worker CPU/RSS UNKNOWN. Only authorized authentication, read/search and exact output writes ran, with exit 0. No Lean/Lake/Cargo/compiler/build, bundled checker, formatter, installation, dependency edits, Git, scratch or generated/cache output. Verification/cache ownership remains primary.

## Artifact and syntax/proof repair

Only Lean artifact: `isolated/native-witness-frame-repair-r9/notes/theory/lean/YulangClosure/NativeExternalEffectFrameR8.lean`, SHA-256 **`747150d9627b84830389ff1b088f43b78da64c3b1f432dbc868a7466b51d1ad9`**. R8 original SHA-256 `0a89a8090650a985c4dd277a4c3c6a2398039ddd7987a2460938b88e0a07a3cc` remains untouched. Only other write is this handoff; no scratch paths.

Escaped the existing reserved identifiers as `«scoped»` and `«partial»`, preserving their identifier meanings; repaired nested record layout in `Effect.apply`, `progressSink` and `writeWord`; annotated `terminal : Segment` to resolve nested constructor expected types. The first two frame terms now expose `State` before case-splitting `Effect`; the native conditional term explicitly composes `congrArg pi represented` with the prefix equality. Other theorem bodies retain their original derivations. No field, constructor, interface, prefix, hypothesis or conclusion was removed or changed. `WriteAll = Writer → Bytes → Reply` is unchanged. The exact `extract` premise is unchanged.

Direct import is only `Init`; no project dependency or root import edits. Authenticated immutable toolchain pin is `leanprover/lean4:v4.35.0`, Lake library `YulangClosure`, process args `-j1 -M1024`, manifest has zero external packages. Actual executable versions **NOT_RUN** by this leaf.

## Exact declarations and audit status

Namespace for every name below: **`YulangClosure.NativeExternalEffectFrameR8`**. Types transcribed from unchanged source statements; kernel-printed types and complete transitive axiom audits are **NOT_RUN** for every declaration. In-file `#print` and `#print axioms` commands remain for all seven.

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

No `sorry`, `admit`, project axiom or checker bypass was introduced. This is a construction statement, not an executed audit. Prior material failure is retained unchanged in R8 `logs/lean.stdout`, SHA-256 `0b5f13235b7c95719ce80a7ce209ceed08882e4d0236f78f86538cde3dc9c689`: parser failures at original lines 148/180/188/206 and uses of `scoped`, expected-type failure at 332, failed `rfl` at 402/406, and all seven recovered declarations contaminated by `sorryAx` (last three also `propext`). R8 check exit 1 is not an R9 receipt.

## Source mapping, represented cases and omissions

Original manuscript: authenticated immutable `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, §§1, 3, 5 (SHA-256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`). Its original shared strategy, source scopes, full supported domain and missing source completeness bridge are retained. The original Simple-sub paper is identified there at §§3.5.1–3.5.2, Figs. 6–9 and §5; that PDF is not in the assigned input set and was not reopened. This repair relies on the unchanged authenticated parent specification and native local footprint, not an imported paper theorem.

Current corrections read: immutable birth-level SCC design §§2–6, SHA-256 `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`, and annotation-effect policy §§1–1.2, SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`. No cross-level qualification or closed annotation-input upper bound was restored. Research drafts remain non-authoritative candidate meaning.

Exact parent Lean definition read: immutable `YulangClosure/Contracts.lean`, SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`, `YulangClosure.SourceProblem.InferenceSoundness`:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The source instance is not supplied by this proposition definition or by `LocalLaws`.

Native source mapping read from immutable root: context `949–992` maps replay operations/drains/processing into `LaunchEvidence`; lib `9253–9265`, `10774–10838`, `11017` onward and publication near `11400–11446` map capacity observation, attempt counter, preparation and publication; lib `20414–20744` maps matrix detachment/restoration and assertions. `incoming_sample_trace.rs:142–238` maps test TLS sample/completed callbacks. `f5c_draft_heap.rs:299–319,378–397,540–554,1000–1027,1150–1168` maps sidecar writes, excluded flush, walker mutation, RELEASE/drop. Hashes are authenticated by the manifest. The full native callback relation is still unconstructed.

Preserved representation includes empty and every finite effect prefix; all arbitrary `WriteAll` progress replies, partial buffer/file progress, swallowed Err, per-word checksum, terminal count overflow, excluded interval assignments, test/production cfg plan choices, attempts overflow, preparation errors, publication, baseline and completed-callback argument/TLS boundaries, matrix detach/restore/RELEASE/drop, unwind and secondary abort. Opaque owner images, caller-supplied complete intermediate plans and exits stay explicit; no successful IO or callback return is assumed. Concrete byte arithmetic, standard-library IO laws, native handle encoding, coherent plan extraction, cfg realization and destructor order remain omitted proof duties, not established instances.

## Parent application and precise open premise

Within this candidate: each `Effect` preserves launch projection; list induction yields all-prefix preservation. The fixed `io`, `changed`, `active` and `p`, together with the unchanged `extract` premise, would yield `pi (view stop) = pi (view start)` for every reached native stop. First bridge remains exactly **`extract` for every actual intermediate native state under one fixed interface/plan**, including partial IO and unwind/drop; owner **primary source/native correspondence lane**. No `extract` instance or source witness is constructed here. The native continuation at `clear_diagnostic_scratch`, seed/enqueue/Running, source/native correspondence and the shared-witness parent remain OPEN. No source case is removed from the parent.

Checks, kernel acceptance, independent review and production authority: **NOT_RUN / PENDING / OPEN**. Next authorized step: primary authenticates these frozen bytes, obtains fresh initial review, then owns its bounded first Lean attempt and complete seven-theorem printed-type/axiom outputs. Only local first-check diagnostics may trigger the packet's one repair revision within the remaining original 600 seconds. No second speculative revision or new scope is claimed.

Writes-stopped receipt: initial candidate and handoff revision 1 frozen; this leaf is **WAITING**, writes stopped pending exact primary diagnostics or STOP. No descendants, generated outputs or unresolved child leases.
