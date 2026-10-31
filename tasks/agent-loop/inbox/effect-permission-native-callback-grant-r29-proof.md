# R29 proof handoff — frozen construction revision 1

Sprint: `EFFECT-PERMISSION-NATIVE-CALLBACK-GRANT/20261030-R29`, contract revision 1,
SHA-256 `8c9784de8a3e33f7e17c2747fcc7e452bda02bb8f4a4a7358c14290642c1457f`.
Assignment: `/root/r29_proof`; handoff revision 1. Session: `R29-20261030`.
Requested model/effort: Sol/high; observed runtime model/effort: UNKNOWN.
Author: this leaf only; no descendants. Outcome: **candidate, constructed but unchecked**.

## Meaning and source scope

Read the original parent in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1, 3, 5 (SHA `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`),
with `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6
(SHA `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`).
The original claim quantifies over every supported original source program,
every lawful finite construction history and retained qualified extrusion,
preserving typing/principal coverage at original scopes with one shared lawful
strategy. This finite callback candidate does not discharge that claim.

`YulangClosure.SourceProblem.InferenceSoundness` in `Contracts.lean` is the
proposition `∀ s x d a, supported s → generates s x d → solves d a →
∃ e, sourceJudgment s x e ∧ sameScoped s x e a`. It supplies no concrete instance.
The applicable effect policy is `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`
§§1.1–1.2, 3–5 (SHA `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`).
Its §6 claimed result is retracted and was not used. The selected R27 callback
source has SHA `163fb480ec7ecaed2c341253066a7c6cc3af1a0cf5499c384f0cad4952c64e18`;
no source/result bytes were altered. Baseline W was admitted by Luna at `4c2b2597d`.
Research drafts and prior R28 receipts supply no semantic authority.

## Source-to-model map

All paths below are under W=`isolated/ep-native-callback-grant-r29/project`.
Runtime files are concurrently owned by Rust, so inspected line numbers are
locators, not final frozen hashes. The final Rust revision/certificate are pending.

- `receiving.rs::CallbackResultSchema::from_parameter`: source annotation/formal
  root ownership; Value callback `() -> [E] int`; concrete nonempty row without
  variables. Its result port is contravariant after the outer formal polarity
  and callback result polarity compose. The selected no-type-argument source is
  represented; generic row/type-argument formation remains OPEN.
- `receiving.rs::callback_entry`: incoming value equality, invocation receiver,
  entry view and formal receipt. `NativeEntry` is an enriched selected record;
  incoming value is copied from the actual view, rather than an emitted effect.
- `machine.rs` operation Apply (`Name(Parameter formal, Observe)`), then
  `receiving.rs::callback_entry_for_apply`: actual resolved formal, direct Name
  receipt/index and source site. These joins are separate from callback_grant.
- `receiving.rs::callback_use`, `callback_execution`, `execution`: typed use,
  result view/receipt and the ordered execution table. `NativeExecution` matches
  native ExecutionView; R26's extra useHandle is recovered from CallbackResult.
- `receiving.rs::observe`, request-owned observations, and `local_grant`:
  `NativeObserved` contains only execution/observer/event. Test-only construction
  bounds are held separately. `ExecutionChecks` joins the selected candidate by
  index to the independent request vector and its bound side evidence.
- `sourceCallbackGrant` transcribes callback_grant's store lookups and positive
  guard, including entry view kind, invocation owner, formal/result receipts,
  source root/occurrence and resolved family membership. Native receipt owners
  represent both ModuleRun and Invocation; selected callback receipts are embedded
  only after owner checks. `StoreJoins` additionally ties Name to receipt_index,
  the actual receipt table and the direct source Name instruction.
- `sourceObservationGrant` uses the production event equality, current
  next_observer inequality, authentic execution-table entry and CallbackResult
  view kind. A construction-time bound is extraction evidence, never an added
  production guard.
- `sourceLocalGrant` transcribes the active-owner check and ordered callback
  prefix of local_grant. RootComp's continuation is arbitrary; the claimed
  positive callback implication holds for every continuation and assumes no
  successful RootComp/native Grant.
- `machine.rs` Catch selection: `NativeCatch.liveInstallations` is the projection
  of selected live dynamic Catch records. Dynamic installation handle, source
  Catch site, owner, selected resolved operation and selected arm remain distinct.
  `CatchChecks` requires actual live membership; projection no longer inserts an
  independently unjoined singleton installation. It retains emitted/pending
  request, active owner, operation/event/payload and exact arm joins.

`siteKey` erases byte spans only; exact source root and occurrence are retained.
SourceEffectId/HirParameterId/operation/root IDs require injective extraction
maps; display names are never identity keys. The same b/request/entry/use and
owner are shared by all conclusions. Consumer result integers are carried but
never assumed equal to 1 or used to prove permission/Grant.

## Artifact and dependency bytes

Changed artifact:
`W/notes/theory/lean/YulangClosure/NativeCallbackGrantBridge.lean`
SHA-256 `e49a320fbb148712b59e27a57cde57072e2192cdcdd84c936b10175f3a6ce6e0`.
Frozen read-only import:
`W/notes/theory/lean/YulangClosure/CallbackHygieneCorrespondence.lean`
SHA-256 `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e`.
Its actual UseReady/PortReady/CatchReady/checkedCatch definitions were read;
no imported model definition was changed.

Scratch authored:
`isolated/ep-native-callback-grant-r29/lean-scratch/AuditNativeCallbackGrantBridge.lean`
SHA-256 `711a9c45def08626a5c85000a786af09d3a9bfd2972c555a2b24efa0852c18cc`.
This contains all ten #check/@ and #print axioms commands, but has never run.
No `.lake` output was written by this leaf.

W pins: lean-toolchain `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`;
lakefile `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`;
manifest `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
The pin is Lean 4.35.0; no external packages.

## Execution and evidence boundary

Actual read-only command from W's Lean project: `elan which lake`, exit 0,
returned `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual Lake/Lean version commands: NOT_RUN. Builds: NOT_RUN. Audits: **0 of 2**,
**0 of 120 audit seconds**. The ten source declarations below are NOT elaborated
or kernel accepted. Printed theorem types: NOT_RUN. Complete transitive axiom
reports: NOT_RUN for every declaration. No compiler/test command was run.

Source search found no sorry/admit term, project axiom, skipKernelTC or
native_decide in the changed bridge/frozen import. The word `admit` matched only
an English comment about ModuleRun. This search is not a transitive axiom audit.
A library-search command initially named the absent Init/Data/Bool directory
(exit 2); it was corrected to the installed `Init/Data/Bool.lean`. No Lean
mathematical diagnostics exist because execution is deliberately gated.

Relevant pinned library sources inspected: Init/Data/List/Lemmas.lean
(`List.mem_of_getElem?`), Init/Prelude.lean (`decide_eq_true`), and
Init/Data/Bool.lean. Original skill checker is available; when authorized, set
TMPDIR to the leased lean-scratch directory so its temporary audit stays in lease,
use the absolute Lake above, --project W/notes/theory/lean,
--module YulangClosure.NativeCallbackGrantBridge, all ten --theorem names below,
and a timeout within the remaining aggregate 120-second/two-audit envelope.
This is a proposed command, not an execution receipt. A fresh Luna stage receipt
must reserve the sole heavyweight slot before any Lake/Lean process starts.

## Source-declared signatures — unchecked

Namespace for all names: `YulangClosure.NativeCallbackGrantBridge`.
These are exact text from the candidate, not printed Lean types. Referenced
validators are explicit constructor/store/request/dynamic Catch joins above;
none is an assumed UseReady, PortReady, CatchReady, History or native success.

```lean
theorem constructor_success_use {e : NativeEntry} {n : NativeName} {u : NativeUse}
    (success : validateConstructors e n u = true) :
    UseReady (entry e) (name n) (callbackUse e n u)

theorem constructor_success_port {b : NativeObservation}
    (constructors : validateConstructors b.entryRecord b.nameRecord b.useRecord = true)
    (execution : validateExecution b = true) :
    PortReady (portSlice b) b.request (permission b.entryRecord)

theorem constructor_success_catch {b : NativeObservation} {c : NativeCatch}
    (constructors : validateConstructors b.entryRecord b.nameRecord b.useRecord = true)
    (execution : validateExecution b = true) (caught : validateCatch b c = true) :
    CatchReady (catchSlice b c) b.request (consumerKey c.consumer) (permission b.entryRecord)

theorem permission_does_not_emit (s : State) (p : Permission) :
    ({s with permissions

theorem constructors_callback_guard {b : NativeObservation}
    (constructors : validateConstructors b.entryRecord b.nameRecord b.useRecord = true)
    (execution : validateExecution b = true)
    (family : b.request.operation.family ∈ b.entryRecord.annotation.families) :
    CallbackGuard b.entryRecord b.useRecord (nativeReceipt b.useRecord.resultReceipt)
      (nativeReceipt b.entryRecord.formalReceipt)
      ⟨b.entryRecord.value, .callbackEntry b.entryRecord.handle⟩
      ⟨b.entryRecord.value, .callbackResult b.useRecord.handle⟩
      b.candidateObservation.execution (.invocation b.entryRecord.receiver)
      b.entryRecord.receiver b.request.operation.family

theorem constructors_callback_decision {s : NativeStore} {b : NativeObservation}
    (constructors : validateConstructors b.entryRecord b.nameRecord b.useRecord = true)
    (execution : validateExecution b = true)
    (stores : validateStoreJoins s b = true)
    (family : b.request.operation.family ∈ b.entryRecord.annotation.families) :
    sourceCallbackGrant s b.useRecord.handle b.candidateObservation.execution
      (.invocation b.entryRecord.receiver) b.entryRecord.receiver
      b.request.operation.family = true

theorem callback_scan_of_member {s : NativeStore} {event : Id .event}
    {owner : NativeOwner} {receiver : Id .invocation} {family : Nat}
    {observations : List NativeObserved} {o : NativeObserved}
    (member : o ∈ observations)
    (grant : sourceObservationGrant s event owner receiver family o = true) :
    sourceCallbackScan s event owner receiver family observations = true

theorem constructors_local_grant {s : NativeStore} {b : NativeObservation}
    (constructors : validateConstructors b.entryRecord b.nameRecord b.useRecord = true)
    (execution : validateExecution b = true)
    (stores : validateStoreJoins s b = true)
    (family : b.request.operation.family ∈ b.entryRecord.annotation.families)
    (rootCompContinuation : Bool) :
    sourceLocalGrant s b.requestObservations b.request.event
      (.invocation b.entryRecord.receiver) b.request.operation.family
      rootCompContinuation = true

theorem constructors_checked_catch {b : NativeObservation} {c : NativeCatch}
    (constructors : validateConstructors b.entryRecord b.nameRecord b.useRecord = true)
    (execution : validateExecution b = true) (caught : validateCatch b c = true) :
    checkedCatch (catchSlice b c) b.request (consumerKey c.consumer)
      (permission b.entryRecord) =
      some ⟨b.request, consumerKey c.consumer, permission b.entryRecord⟩

theorem constructors_callback_and_catch {s : NativeStore} {b : NativeObservation}
    {c : NativeCatch}
    (constructors : validateConstructors b.entryRecord b.nameRecord b.useRecord = true)
    (execution : validateExecution b = true)
    (stores : validateStoreJoins s b = true)
    (caught : validateCatch b c = true)
    (rootCompContinuation : Bool) :
    PortReady (catchSlice b c) b.request (permission b.entryRecord) ∧
    sourceLocalGrant s b.requestObservations b.request.event
      (.invocation b.entryRecord.receiver) b.request.operation.family
      rootCompContinuation = true ∧
    checkedCatch (catchSlice b c) b.request (consumerKey c.consumer)
      (permission b.entryRecord) =
      some ⟨b.request, consumerKey c.consumer, permission b.entryRecord⟩
```

## Parent application and first remaining premise

`constructors_callback_and_catch` is intended to apply all component results to
one shared callback record bundle and the actual R26 checkedCatch decision.
It would reduce the bounded callback application to concrete successes of
validateConstructors, validateExecution, validateStoreJoins and validateCatch.
That reduction is currently constructed only; kernel acceptance is absent.

First remaining request `R29-CALLBACK-CONCRETE-1`, owner Rust/Luna: freeze and
provide the authenticated callback certificate and final source hashes, its
independent request-owned vector/construction-bound evidence, exact source/store
joins, injective ID map and selected dynamic installation/arm. **Final certificate
hash: NOT_AVAILABLE to this leaf.** Then Luna supplies a fresh serial audit-stage
receipt; this leaf can construct the concrete instance and repair against actual
diagnostics within the original budget. Falsifier: any authenticated selected
record fails a required join, a native successful callback branch fails the
projected guard, or concrete application requires an unsupported source premise.
Stop at that first boundary rather than assume the premise.

No authenticated History from `{}` has been constructed or assumed, so R26's
generated_selection_actual/conservation consequences that require History are
not applied. Full RootComp/computation-formal route, generic symbolic rows and
type arguments, continuation replay, source generation/propagation, original
A/B, whole-language hygiene/soundness, shared source strategy, principality,
termination, independent review and production authority remain OPEN. The
companion result 23 is not used as callback/Grant evidence.

## Resource and stopped-writing receipt

The fixed construction envelope is 1400 seconds. Primary owns the authoritative
launch-time receipt; current.json exposes no elapsed start timestamp to this
leaf. First explicit leaf clock read: 2026-10-29 23:21:09 UTC; the construction
freeze follows at approximately 23:28 UTC, plus unclocked startup/source reads.
No elapsed-budget reset or invented exact remainder is claimed. Heavy process
count: 0; Lean/Lake audit count: 0; descendants: none; Git mutations: none.

State: **STOPPED at certificate/audit-stage boundary**. Writes stop on submission
of this revision. Exact written paths are the bridge, the one scratch audit above,
and this handoff; `.lake` untouched. No worker/cache process remains active.
The source candidate is frozen for intake, not independently reviewed or accepted.
Resume only on Luna's fresh current-session receipt and final certificate hash.
