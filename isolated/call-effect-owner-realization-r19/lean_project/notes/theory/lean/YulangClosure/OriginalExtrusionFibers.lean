import YulangClosure.OriginalExtrusionWork
import YulangClosure.OriginalBoundFibers

/-!
Compute the complete transported relation key for the real extrusion Bound
request, then apply the same physical interner/attachment suffix. This fills
the key-construction input of OriginalBoundFibers.publish. Authentic native
representative/discharge readouts and the prior snapshot/evidence machinery
remain explicit extraction obligations; no complete NQ or inference theorem
is claimed by the successful local computation.
-/
namespace YulangClosure.OriginalExtrusionFibers

open OriginalExtrusionWork (Endpoint RawBound BoundRequest)
open NativeValuePorts (Pair Key Flow ValueEndpoint)
open NativeContextExpansion (ScopedDemand)
namespace F
export OriginalBoundFibers (Store Valid Physical PublicationResources PublicationOutcome
  publish publish_valid published_fiber_exact fibers walk)
end F

inductive Failure where
  | kindViolation | missingParent | receiptMismatch
  deriving DecidableEq, Repr

/-- Native bound_pair retains both endpoint kinds and the polarity swap.
Cross-kind raw keys are represented as the native invariant-violation case. -/
def boundPair (bound : RawBound) : Except Failure Pair :=
  match bound.owner, bound.endpoint with
  | .value owner, .value item =>
    .ok (match bound.polarity with
      | .positive => .value item owner
      | .negative => .value owner item)
  | .effect owner, .effect item =>
    .ok (match bound.polarity with
      | .positive => .effect item owner
      | .negative => .effect owner item)
  | _, _ => .error .kindViolation

/-- The native two-position loop checks owner before endpoint, and breaks
after the first matching negative Function root. A wrong-kind replacement
fails; it is not ignored in favor of the second position. -/
def remapRoot (original destination : RawBound) (root : Nat) : Except Failure Nat :=
  if original.owner = .value (.negativeFunction root) then
    match destination.owner with
    | .value (.negativeFunction fresh) => .ok fresh
    | _ => .error .receiptMismatch
  else if original.endpoint = .value (.negativeFunction root) then
    match destination.endpoint with
    | .value (.negativeFunction fresh) => .ok fresh
    | _ => .error .receiptMismatch
  else .ok root

def remapFlow (original destination : RawBound) (flow : Flow) : Except Failure Flow :=
  match flow.demand with
  | none => .ok flow
  | some demand =>
    match remapRoot original destination demand.root with
    | .error failure => .error failure
    | .ok root => .ok {flow with demand := some {demand with root := root}}

def metadata (flow : Flow) : Nat × Option (Nat × Nat × Nat × Nat) :=
  (flow.transformer, flow.demand.map fun demand =>
    (demand.originalCall, demand.useInstance, demand.outputScope, demand.inputRoute))

theorem remap_flow_metadata {original destination : RawBound} {before after : Flow}
    (computed : remapFlow original destination before = .ok after) :
    metadata after = metadata before := by
  cases demanded : before.demand with
  | none =>
    have same : before = after := by simpa [remapFlow, demanded] using computed
    subst after
    rfl
  | some demand =>
    cases remapped : remapRoot original destination demand.root with
    | error failure => simp [remapFlow, demanded, remapped] at computed
    | ok root =>
      have same : {before with demand := some {demand with root := root}} = after := by
        simpa [remapFlow, demanded, remapped] using computed
      subst after
      simp [metadata, demanded]

structure Readout where
  valueRepresentative : Nat → Nat
  effectRepresentative : Nat → Nat
  discharged : Nat → Bool
  dischargeResidual : Nat → Option Nat

/-- The same native parent ID selects discharge and residual; absence of a
residual at a discharged parent is the actual IDENTITY=0 branch. -/
def postContext (readout : Readout) (parent context : Nat) : Nat :=
  if readout.discharged parent then (readout.dischargeResidual parent).getD 0 else context

def transportKey (native : NativeRelationInterner.Native) (readout : Readout)
    (request : BoundRequest) (parent : Nat) : Except Failure Key := do
  let pair ← boundPair request.destination
  let source ← match native.store.readback parent with
    | none => .error .missingParent
    | some key => .ok key
  let flow ← remapFlow request.original request.destination source.flow
  .ok ⟨pair.rename readout.valueRepresentative readout.effectRepresentative,
    postContext readout parent source.context, source.sources, flow⟩

theorem transport_key_exact {native : NativeRelationInterner.Native} {readout : Readout}
    {request : BoundRequest} {parent : Nat} {key : Key}
    (computed : transportKey native readout request parent = .ok key) :
    ∃ source pair flow,
      native.store.readback parent = some source ∧
      boundPair request.destination = .ok pair ∧
      remapFlow request.original request.destination source.flow = .ok flow ∧
      key = ⟨pair.rename readout.valueRepresentative readout.effectRepresentative,
        postContext readout parent source.context, source.sources, flow⟩ ∧
      metadata key.flow = metadata source.flow := by
  cases paired : boundPair request.destination with
  | error failure => simp [transportKey, paired, bind, Except.bind] at computed
  | ok pair =>
    cases stored : native.store.readback parent with
    | none => simp [transportKey, paired, stored, bind, Except.bind] at computed
    | some source =>
      cases mapped : remapFlow request.original request.destination source.flow with
      | error failure => simp [transportKey, paired, stored, mapped, bind, Except.bind] at computed
      | ok flow =>
        have same :
            (⟨pair.rename readout.valueRepresentative readout.effectRepresentative,
              postContext readout parent source.context, source.sources, flow⟩ : Key) = key := by
          simpa [transportKey, paired, stored, mapped, bind, Except.bind] using computed
        subst key
        exact ⟨source, pair, flow, rfl, rfl, mapped, rfl, remap_flow_metadata mapped⟩

inductive Outcome where
  | keyFailure (failure : Failure)
  | published (outcome : F.PublicationOutcome)
  deriving DecidableEq, Repr

def transfer (state : F.Physical RawBound) (valid : F.Valid state.fibers)
    (readout : Readout) (resources : F.PublicationResources)
    (request : BoundRequest) (parent : Nat) : F.Physical RawBound × Outcome :=
  match transportKey state.native readout request parent with
  | .error failure => (state, .keyFailure failure)
  | .ok key =>
    let published := F.publish state valid resources request.destination key
    (published.1, .published published.2)

theorem transfer_valid (state : F.Physical RawBound) (valid : F.Valid state.fibers)
    (readout : Readout) (resources : F.PublicationResources)
    (request : BoundRequest) (parent : Nat) :
    F.Valid (transfer state valid readout resources request parent).1.fibers := by
  cases keyed : transportKey state.native readout request parent with
  | error failure => simpa only [transfer, keyed] using valid
  | ok key => simpa only [transfer, keyed] using F.publish_valid state valid resources request.destination key

/-- Complete source lookup and native key construction supply the authentic
input to the physical publication theorem, all at this same Bound request.
The result keeps the original source-set and four non-root demand fields;
the fifth field changes only by the actual two-position root remapping. -/
theorem transferred_fiber_exact (state : F.Physical RawBound) (valid : F.Valid state.fibers)
    (history : NativeRelationInterner.NativeHistory state.native)
    (readout : Readout) (resources : F.PublicationResources)
    (request : BoundRequest) (parent relation : Nat)
    (normal : (transfer state valid readout resources request parent).2 =
      .published (.complete relation)) :
    ∃ source pair flow key,
      state.native.store.readback parent = some source ∧
      boundPair request.destination = .ok pair ∧
      remapFlow request.original request.destination source.flow = .ok flow ∧
      key = ⟨pair.rename readout.valueRepresentative readout.effectRepresentative,
        postContext readout parent source.context, source.sources, flow⟩ ∧
      NativeValuePorts.Allowed key ∧ metadata key.flow = metadata source.flow ∧
      (transfer state valid readout resources request parent).1.native.store.readback relation = some key ∧
      relation ∈ F.fibers (transfer state valid readout resources request parent).1.fibers
        (transfer_valid state valid readout resources request parent) request.destination := by
  cases keyed : transportKey state.native readout request parent with
  | error failure => simp [transfer, keyed] at normal
  | ok key =>
    have published : (F.publish state valid resources request.destination key).2 = .complete relation := by
      simpa [transfer, keyed] using normal
    obtain ⟨source, pair, flow, stored, paired, mapped, shape, fields⟩ := transport_key_exact keyed
    obtain ⟨allowed, readback, member⟩ :=
      F.published_fiber_exact state valid history resources request.destination key published
    refine ⟨source, pair, flow, key, stored, paired, mapped, shape, allowed, fields, ?_, ?_⟩
    · simpa only [transfer, keyed] using readback
    · simpa only [transfer, keyed] using member

theorem transfer_captured_source (state : F.Physical RawBound) (valid : F.Valid state.fibers)
    (readout : Readout) (resources : F.PublicationResources)
    (request : BoundRequest) (parent : Nat) :
    F.walk (transfer state valid readout resources request parent).1.fibers.entries
      (transfer_valid state valid readout resources request parent).backward
      (state.fibers.heads request.original) =
      F.walk state.fibers.entries valid.backward (state.fibers.heads request.original) := by
  cases keyed : transportKey state.native readout request parent with
  | error failure => simp only [transfer, keyed]
  | ok key =>
    simpa only [transfer, keyed] using OriginalBoundFibers.publish_captured_source
      state valid resources request.destination request.original key

/-- Every error and success preserves the same forward native call history;
no cancellation or replacement of a raw relation occurs inside this suffix. -/
theorem transfer_native_run (state : F.Physical RawBound) (valid : F.Valid state.fibers)
    (readout : Readout) (resources : F.PublicationResources)
    (request : BoundRequest) (parent : Nat) :
    NativeRelationInterner.NativeRun state.native
      (transfer state valid readout resources request parent).1.native := by
  cases keyed : transportKey state.native readout request parent with
  | error failure =>
    simp only [transfer, keyed]
    exact .nil _
  | ok key =>
    simp only [transfer, keyed, OriginalBoundFibers.publish_native]
    exact .call (.nil _) resources.interner key

theorem transfer_fiber_run (state : F.Physical RawBound) (valid : F.Valid state.fibers)
    (readout : Readout) (resources : F.PublicationResources)
    (request : BoundRequest) (parent : Nat) :
    OriginalBoundFibers.Run state.fibers
      (transfer state valid readout resources request parent).1.fibers := by
  cases keyed : transportKey state.native readout request parent with
  | error failure =>
    simp only [transfer, keyed]
    exact .nil _
  | ok key =>
    simpa only [transfer, keyed] using OriginalBoundFibers.publish_fiber_run
      state valid resources request.destination key

theorem transfer_history (state : F.Physical RawBound) (valid : F.Valid state.fibers)
    (history : NativeRelationInterner.NativeHistory state.native)
    (readout : Readout) (resources : F.PublicationResources)
    (request : BoundRequest) (parent : Nat) :
    NativeRelationInterner.NativeHistory
      (transfer state valid readout resources request parent).1.native :=
  .commit history (transfer_native_run state valid readout resources request parent)

theorem transfer_old_readback (state : F.Physical RawBound) (valid : F.Valid state.fibers)
    (history : NativeRelationInterner.NativeHistory state.native)
    (readout : Readout) (resources : F.PublicationResources)
    (request : BoundRequest) (parent relation : Nat) (key : Key)
    (old : state.native.store.readback relation = some key) :
    (transfer state valid readout resources request parent).1.native.store.readback relation = some key := by
  obtain ⟨coherent, projected⟩ := NativeRelationInterner.native_history_refinement history
  exact NativeRelationInterner.old_relation_readback projected
    (NativeRelationInterner.native_run_refinement
      (transfer_native_run state valid readout resources request parent) coherent).2 old

theorem transfer_preserves_fiber (state : F.Physical RawBound) (valid : F.Valid state.fibers)
    (readout : Readout) (resources : F.PublicationResources)
    (request : BoundRequest) (parent : Nat) (bound : RawBound) (relation : Nat)
    (old : relation ∈ F.fibers state.fibers valid bound) :
    relation ∈ F.fibers (transfer state valid readout resources request parent).1.fibers
      (transfer_valid state valid readout resources request parent) bound :=
  OriginalBoundFibers.run_preserves_fiber
    (transfer_fiber_run state valid readout resources request parent) valid bound relation old

end YulangClosure.OriginalExtrusionFibers
