import YulangClosure.OriginalFiberTransfer

/-!
The scoped Value branch of the actual selected extrusion Bound: metadata
admission precedes the physical append; readback, Value capture (a no-op),
dirty/emission and sampling precede the first executable-fiber loop. The
loop receives the SAME retained physical state. Its complete result stops
before the later origin-metadata loop, not at full Work completion.

Opaque insertion-bookkeeping readouts may retain partial changes even when
a call fails. They cannot replace either the Work store or the native
relation/fiber store. The unscoped OwnerEmission branch can seed executable
fibers and is an explicit external owner, not the scoped relation=None case.
-/
namespace YulangClosure.OriginalBoundWorkExecution

open OriginalExtrusionWork (Endpoint RawBound BoundRequest Operation)
open NativeValuePorts (ValueEndpoint Pair Key)
open NativeMergeExpansion (Polarity)

namespace W
export OriginalExtrusionWork (State Result External Funding funded step runPrefix physicalInsert boundRequest)
end W
namespace TF
export OriginalFiberTransfer (State Inputs Parameters Result Call Outcome transferBound Delivered bound_complete)
end TF
namespace F
export OriginalBoundFibers (Physical Store Valid fibers walk)
end F

inductive Lane where
  | rows | atoms

structure Slot where
  owner : Nat
  polarity : Polarity
  lane : Lane
  index : Nat

inductive Site where
  | snapshot | admission | reserveEmission | journal | capacity
  | append | accounting | readback | capture | emission | sample

inductive Failure where
  | identityExhausted | receiptMismatch
  | native (site : Site) (code : Nat)
  | physical (failure : OriginalExtrusionWork.Failure)

/-- A scoped BoundTransport admission has no executable relation. Its full
request, antecedent and actual origin pair remain ordinary data. -/
structure Admission where
  request : BoundRequest
  antecedent : Nat
  origin : Pair
  relation : Option Nat := none

def scopedAdmission (request : BoundRequest) (antecedent : Nat)
    (scope : Option Pair) (pair : Pair) : Admission :=
  ⟨request, antecedent, scope.getD pair, none⟩

theorem scoped_admission_whole (request : BoundRequest) (antecedent : Nat)
    (scope : Option Pair) (pair : Pair) :
    (scopedAdmission request antecedent scope pair).relation = none ∧
    (scopedAdmission request antecedent scope pair).request = request ∧
    (scopedAdmission request antecedent scope pair).antecedent = antecedent ∧
    (scopedAdmission request antecedent scope pair).origin = scope.getD pair :=
  ⟨rfl, rfl, rfl, rfl⟩

structure Emission where
  id : Nat
  admission : Nat
  slot : Slot
  bound : RawBound

/-- This is an external metadata-owner readout, not a semantic certificate.
The returned bookkeeping is retained on both success and error. -/
structure Observation (M : Type) (A : Type) where
  bookkeeping : M
  result : Except Nat A

structure Calls (M : Type) where
  contextPresent : Bool := true
  snapshot : M → RawBound → Observation M Nat
  admission : M → Admission → Observation M Nat
  reserveEmission : M → Observation M Unit
  journal : M → Slot → Observation M Unit
  capacity : M → Slot → Observation M Unit
  /-- Infallible flags/counter updates immediately after the physical push. -/
  accounting : M → Slot → RawBound → M
  emission : M → Nat → Slot → RawBound → M × Nat
  /-- Includes the subsequent test-only emission probe when it is enabled. -/
  sample : M → Observation M Unit

structure State (M : Type) where
  work : W.State
  transfer : TF.State
  scopedEnabled : Bool := true
  scope : Option Pair := none
  /-- Current insertion readout; retained as a before-loop checkpoint after
  the separately owned TF loop starts. No claim is made that TF leaves its
  opaque evidence/dependency metadata unchanged. -/
  bookkeeping : M
  dirty : Bool := false
  emissions : List Emission := []
  trace : List Site := []

inductive InsertOutcome where
  | ready (slot : Slot)
  | failed (failure : Failure)
  | unscopedOwnerEmission
  | effectOwner (antecedent : Nat)

structure InsertResult (M : Type) where
  state : State M
  request : BoundRequest
  outcome : InsertOutcome

def failed (state : State M) (request : BoundRequest) (failure : Failure) : InsertResult M :=
  ⟨state, request, .failed failure⟩

def observe (state : State M) (request : BoundRequest) (site : Site)
    (observation : Observation M A) (next : A → State M → InsertResult M) : InsertResult M :=
  let after := {state with bookkeeping := observation.bookkeeping, trace := state.trace ++ [site]}
  match observation.result with
  | .error code => failed after request (.native site code)
  | .ok value => next value after

def valueRows (p : Polarity) (row : OriginalExtrusionWork.Bounds ValueEndpoint) : List Nat :=
  match p with | .positive => row.lowerRows | .negative => row.upperRows

def valueAtoms (p : Polarity) (row : OriginalExtrusionWork.Bounds ValueEndpoint) : List ValueEndpoint :=
  match p with | .positive => row.lowerAtoms | .negative => row.upperAtoms

/-- The actual addressed Value-vector readback, not a supplied matching key. -/
def readback (work : W.State) (slot : Slot) : Option RawBound := do
  let row ← work.values[slot.owner]?
  let endpoint ← match slot.lane with
    | .rows => (valueRows slot.polarity row)[slot.index]?.map ValueEndpoint.row
    | .atoms => (valueAtoms slot.polarity row)[slot.index]?
  return ⟨.value (.row slot.owner), slot.polarity, .value endpoint⟩

/-- The native kind/owner/length checks precede origin admission. `none`
names the separately owned Effect insertion, not a successful Value result. -/
def locate (work : W.State) (bound : RawBound) : Except Failure (Option Slot) :=
  match bound.owner, bound.endpoint with
  | .value (.row owner), .value endpoint =>
      match work.values[owner]? with
      | none => .error .identityExhausted
      | some row => .ok (some ⟨owner, bound.polarity,
          match endpoint with | .row _ => .rows | _ => .atoms,
          match endpoint with
          | .row _ => (valueRows bound.polarity row).length
          | _ => (valueAtoms bound.polarity row).length⟩)
  | .effect (.row owner), .effect _ =>
      if (work.effects[owner]?).isSome then .ok none else .error .identityExhausted
  | _, _ => .error .identityExhausted

def canonicalRequest (work : W.State) (request : BoundRequest) : BoundRequest :=
  {request with destination := work.canonicalBound request.insertion}

/-- Value capture registration is a no-op; the remaining publication calls
are kept after physical readback and before the insertion returns. -/
def finishValue (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) (bound : RawBound) : InsertResult M :=
  let captured : State M := {state with trace :=
    if request.capture then state.trace ++ [Site.capture] else state.trace}
  let marked : State M := {captured with dirty := true}
  let emitted := calls.emission marked.bookkeeping admission slot bound
  let published : State M := {marked with
    bookkeeping := emitted.1
    emissions := marked.emissions ++ [⟨emitted.2, admission, slot, bound⟩]
    trace := marked.trace ++ [Site.emission]}
  observe published request .sample (calls.sample published.bookkeeping)
    fun _ sampled => ⟨sampled, request, .ready slot⟩

/-- The caller enters only the computed Value branch. Native capture
registration only matches an Effect-row/negative/Allowance bound. -/
def appendValue (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) : InsertResult M :=
  match W.physicalInsert state.work request.insertion with
  | .error failure => failed state request (.physical failure)
  | .ok work =>
      let written : State M := {state with work := work, trace := state.trace ++ [Site.append]}
      let counted : State M := {written with
        bookkeeping := calls.accounting written.bookkeeping slot request.destination
        trace := written.trace ++ [Site.accounting]}
      let checked : State M := {counted with trace := counted.trace ++ [Site.readback]}
      match readback work slot with
      | none => failed checked request .receiptMismatch
      | some bound =>
          if bound ≠ request.destination then failed checked request .receiptMismatch
          else finishValue calls checked request slot admission bound

def reserveAndAppend (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) : InsertResult M :=
  observe state request .capacity (calls.capacity state.bookkeeping slot) fun _ after =>
    appendValue calls after request slot admission

def journalAndAppend (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) : InsertResult M :=
  observe state request .journal (calls.journal state.bookkeeping slot) fun _ after =>
    reserveAndAppend calls after request slot admission

def admitted (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) : InsertResult M :=
  observe state request .reserveEmission (calls.reserveEmission state.bookkeeping) fun _ after =>
    journalAndAppend calls after request slot admission

def imported (calls : Calls M) (state : State M) (request : BoundRequest)
    (antecedent : Nat) : InsertResult M :=
  match locate state.work request.destination with
  | .error failure => failed state request failure
  | .ok none => ⟨state, request, .effectOwner antecedent⟩
  | .ok (some slot) =>
      match OriginalExtrusionFibers.boundPair request.destination with
      | .error _ => failed state request .identityExhausted
      | .ok pair =>
          let admission := scopedAdmission request antecedent state.scope pair
          observe state request .admission (calls.admission state.bookkeeping admission) fun id after =>
            admitted calls after request slot id

/-- Source order: import snapshot, compute the canonical physical lane,
scoped relation=None admission, reserve emission, journal/capacity, append,
readback/capture/dirty/emission/sample. No arbitrary post-insertion state is
an input. In unscoped mode OwnerEmission must run before any append. -/
def insert (calls : Calls M) (state : State M) (original : BoundRequest) : InsertResult M :=
  let request := canonicalRequest state.work original
  if calls.contextPresent = false then failed state request .identityExhausted else
  if state.scopedEnabled = false then ⟨state, request, .unscopedOwnerEmission⟩ else
  observe state request .snapshot (calls.snapshot state.bookkeeping request.original) fun antecedent after =>
    imported calls after request antecedent

/-- Canonical representatives come from this SAME Work state. The external
loop readout supplies discharge/residual and resource data, never unrelated
Value/Effect representatives. -/
def loopInputs (work : W.State) (inputs : TF.Inputs) : TF.Inputs :=
  fun physical index parent =>
    let observed := inputs physical index parent
    {observed with readout := {observed.readout with
      valueRepresentative := work.qv, effectRepresentative := work.qe}}

inductive Outcome where
  | workNext | workExternal | workFailed
  | insertionFailed | unscopedOwnerEmission | effectOwner
  | fiberFailure (failure : TF.Outcome)
  /-- First executable-fiber loop finished; origin-metadata loop is next. -/
  | originMetadata
  deriving DecidableEq

structure Result (M : Type) where
  state : State M
  request : Option BoundRequest := none
  slot : Option Slot := none
  calls : List TF.Call := []
  outcome : Outcome
  insertion : Option (InsertResult M) := none
  workResult : Option W.Result := none

def continueBound (calls : Calls M) (inputs : TF.Inputs) (state : State M)
    (request : BoundRequest) : Result M :=
  let inserted := insert calls state request
  match inserted.outcome with
  | .failed _ => ⟨inserted.state, some inserted.request, none, [], .insertionFailed, some inserted, none⟩
  | .unscopedOwnerEmission =>
      ⟨inserted.state, some inserted.request, none, [], .unscopedOwnerEmission, some inserted, none⟩
  | .effectOwner _ => ⟨inserted.state, some inserted.request, none, [], .effectOwner, some inserted, none⟩
  | .ready slot =>
      let transferred := TF.transferBound (loopInputs inserted.state.work inputs)
        inserted.request inserted.state.transfer
      let after := {inserted.state with transfer := transferred.state}
      ⟨after, some inserted.request, some slot, transferred.calls,
        match transferred.outcome with
        | .complete => .originMetadata
        | other => .fiberFailure other,
        some inserted, none⟩

def continueWork (calls : Calls M) (inputs : TF.Inputs) (state : State M)
    (result : W.Result) : Result M :=
  match result with
  | .next work => ⟨{state with work := work}, none, none, [], .workNext, none, some result⟩
  | .failed work _ => ⟨{state with work := work}, none, none, [], .workFailed, none, some result⟩
  | .external work (.bound request) => continueBound calls inputs {state with work := work} request
  | .external work _ => ⟨{state with work := work}, none, none, [], .workExternal, none, some result⟩

def execute (calls : Calls M) (inputs : TF.Inputs) (funds : W.Funding) (state : State M) : Result M :=
  continueWork calls inputs state (W.step funds state.work)

/-! Local facts from the actual insertion computation. -/

theorem canonical_request_whole (work : W.State) (request : BoundRequest) :
    (canonicalRequest work request).original = request.original ∧
    (canonicalRequest work request).insertion = request.insertion ∧
    (canonicalRequest work request).operation = request.operation ∧
    (canonicalRequest work request).capture = request.capture ∧
    (canonicalRequest work request).destination = work.canonicalBound request.insertion :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem selected_request_canonical (work : W.State) (owner : Endpoint)
    (polarity : Polarity) (copied : Endpoint) (original : RawBound) :
    canonicalRequest work (W.boundRequest work owner polarity copied original) =
      W.boundRequest work owner polarity copied original := rfl

theorem loop_inputs_representatives (work : W.State) (inputs : TF.Inputs)
    (physical : F.Physical RawBound) (index parent : Nat) :
    ((loopInputs work inputs) physical index parent).readout.valueRepresentative = work.qv ∧
    ((loopInputs work inputs) physical index parent).readout.effectRepresentative = work.qe := ⟨rfl, rfl⟩

theorem unscoped_stops (calls : Calls M) (state : State M) (request : BoundRequest)
    (present : calls.contextPresent = true) (unscoped : state.scopedEnabled = false) :
    insert calls state request =
      ⟨state, canonicalRequest state.work request, .unscopedOwnerEmission⟩ := by
  simp [insert, present, unscoped]

theorem physical_representatives {before after : W.State} {bound : RawBound}
    (computed : W.physicalInsert before bound = .ok after) :
    after.qv = before.qv ∧ after.qe = before.qe := by
  unfold OriginalExtrusionWork.physicalInsert at computed
  dsimp only at computed
  split at computed
  · simp only [OriginalExtrusionWork.requireSome, bind, Except.bind] at computed
    split at computed <;> cases computed
    exact ⟨rfl, rfl⟩
  · simp only [OriginalExtrusionWork.requireSome, bind, Except.bind] at computed
    split at computed <;> cases computed
    exact ⟨rfl, rfl⟩
  · cases computed

def Retains (physical : TF.State) (request : BoundRequest) (result : InsertResult M) : Prop :=
  result.state.transfer = physical ∧ result.request = request

theorem observe_retains (state : State M) (request : BoundRequest) (site : Site)
    (observation : Observation M A) (next : A → State M → InsertResult M)
    (continuation : ∀ value, Retains state.transfer request
      (next value {state with bookkeeping := observation.bookkeeping, trace := state.trace ++ [site]})) :
    Retains state.transfer request (observe state request site observation next) := by
  unfold observe
  cases observation.result with
  | error code => exact ⟨rfl, rfl⟩
  | ok value => exact continuation value

theorem finish_retains (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) (bound : RawBound) :
    Retains state.transfer request (finishValue calls state request slot admission bound) := by
  unfold finishValue
  apply observe_retains
  intro value
  exact ⟨rfl, rfl⟩

theorem append_retains (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) :
    Retains state.transfer request (appendValue calls state request slot admission) := by
  unfold appendValue
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · exact finish_retains calls _ request slot admission _

theorem reserve_retains (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) :
    Retains state.transfer request (reserveAndAppend calls state request slot admission) := by
  unfold reserveAndAppend
  apply observe_retains
  intro value
  exact append_retains calls _ request slot admission

theorem journal_retains (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) :
    Retains state.transfer request (journalAndAppend calls state request slot admission) := by
  unfold journalAndAppend
  apply observe_retains
  intro value
  exact reserve_retains calls _ request slot admission

theorem admitted_retains (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) :
    Retains state.transfer request (admitted calls state request slot admission) := by
  unfold admitted
  apply observe_retains
  intro value
  exact journal_retains calls _ request slot admission

theorem imported_retains (calls : Calls M) (state : State M) (request : BoundRequest)
    (antecedent : Nat) : Retains state.transfer request (imported calls state request antecedent) := by
  unfold imported
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · apply observe_retains
      intro value
      exact admitted_retains calls _ request _ value

theorem insert_retains (calls : Calls M) (state : State M) (request : BoundRequest) :
    Retains state.transfer (canonicalRequest state.work request) (insert calls state request) := by
  unfold insert
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · apply observe_retains
      intro value
      exact imported_retains calls _ _ value

theorem insert_fibers_unchanged (calls : Calls M) (state : State M) (request : BoundRequest) :
    (insert calls state request).state.transfer = state.transfer :=
  (insert_retains calls state request).1

theorem insert_request (calls : Calls M) (state : State M) (request : BoundRequest) :
    (insert calls state request).request = canonicalRequest state.work request :=
  (insert_retains calls state request).2

theorem finish_retained (calls : Calls M) (state : State M)
    (request : BoundRequest) (slot : Slot) (admission : Nat) (bound : RawBound) :
    (finishValue calls state request slot admission bound).state.work = state.work ∧
    (finishValue calls state request slot admission bound).state.dirty = true := by
  unfold finishValue observe failed
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

theorem finish_ready_slot (calls : Calls M) (state : State M)
    (request : BoundRequest) (slot : Slot) (admission : Nat) (bound : RawBound)
    (returned : Slot)
    (normal : (finishValue calls state request slot admission bound).outcome = .ready returned) :
    returned = slot := by
  unfold finishValue observe failed at normal
  dsimp only at normal
  split at normal
  · cases normal
  · cases normal
    rfl

theorem append_ready_readback (calls : Calls M) (state : State M)
    (request : BoundRequest) (slot : Slot) (admission : Nat) (returned : Slot)
    (normal : (appendValue calls state request slot admission).outcome = .ready returned) :
    readback (appendValue calls state request slot admission).state.work returned = some request.destination ∧
    (appendValue calls state request slot admission).state.dirty = true ∧
    (appendValue calls state request slot admission).state.work.qv = state.work.qv ∧
    (appendValue calls state request slot admission).state.work.qe = state.work.qe := by
  unfold appendValue at normal ⊢
  cases inserted : W.physicalInsert state.work request.insertion with
  | error failure => simp [inserted, failed] at normal
  | ok after =>
    simp only [inserted] at normal ⊢
    try dsimp only at normal ⊢
    cases stored : readback after slot with
    | none => simp [stored, failed] at normal
    | some bound =>
      simp only [stored] at normal ⊢
      by_cases mismatch : bound ≠ request.destination
      · simp [mismatch, failed] at normal
      · simp only [mismatch, ↓reduceIte] at normal ⊢
        have same := finish_ready_slot calls _ request slot admission bound returned normal
        subst returned
        obtain ⟨kept, dirty⟩ := finish_retained calls _ request slot admission bound
        obtain ⟨values, effects⟩ := physical_representatives inserted
        refine ⟨?_, dirty, ?_, ?_⟩
        · rw [kept]
          exact stored.trans (congrArg some (Classical.byContradiction mismatch))
        · rw [kept]
          exact values
        · rw [kept]
          exact effects

/-- This proposition is proved from the computation; it is never an input
field of the machine or of its external call readouts. -/
def ValueReady (before : W.State) (request : BoundRequest) (result : InsertResult M) : Prop :=
  ∀ slot, result.outcome = .ready slot →
    readback result.state.work slot = some request.destination ∧
    result.state.dirty = true ∧ result.state.work.qv = before.qv ∧
    result.state.work.qe = before.qe

theorem observe_ready (state : State M) (request : BoundRequest) (site : Site)
    (observation : Observation M A) (next : A → State M → InsertResult M)
    (before : W.State)
    (continuation : ∀ value, ValueReady before request
      (next value {state with bookkeeping := observation.bookkeeping, trace := state.trace ++ [site]})) :
    ValueReady before request (observe state request site observation next) := by
  unfold observe
  cases observed : observation.result with
  | error code => intro slot normal; cases normal
  | ok value => exact continuation value

theorem reserve_ready (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) :
    ValueReady state.work request (reserveAndAppend calls state request slot admission) := by
  unfold reserveAndAppend
  apply observe_ready
  intro value returned normal
  exact append_ready_readback calls _ request slot admission returned normal

theorem journal_ready (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) :
    ValueReady state.work request (journalAndAppend calls state request slot admission) := by
  unfold journalAndAppend
  apply observe_ready
  intro value
  exact reserve_ready calls _ request slot admission

theorem admitted_ready (calls : Calls M) (state : State M) (request : BoundRequest)
    (slot : Slot) (admission : Nat) :
    ValueReady state.work request (admitted calls state request slot admission) := by
  unfold admitted
  apply observe_ready
  intro value
  exact journal_ready calls _ request slot admission

theorem imported_ready (calls : Calls M) (state : State M) (request : BoundRequest)
    (antecedent : Nat) : ValueReady state.work request (imported calls state request antecedent) := by
  unfold imported
  split
  · intro slot normal; cases normal
  · intro slot normal; cases normal
  · split
    · intro slot normal; cases normal
    · apply observe_ready
      intro value
      exact admitted_ready calls _ request _ value

theorem insert_ready (calls : Calls M) (state : State M) (request : BoundRequest) :
    ValueReady state.work (canonicalRequest state.work request) (insert calls state request) := by
  unfold insert
  dsimp only
  split
  · intro slot normal; cases normal
  · split
    · intro slot normal; cases normal
    · apply observe_ready
      intro value
      exact imported_ready calls _ _ value

/-- Output at the named cut immediately before the later metadata loop.
The captured list is taken from the original physical table, not supplied as
an allegedly completed fiber list. Every delivered key remains complete. -/
def AtOriginMetadata (before : State M) (request : BoundRequest) (result : Result M) : Prop :=
  ∃ slot,
    result.request = some (canonicalRequest before.work request) ∧
    result.slot = some slot ∧
    readback result.state.work slot = some (canonicalRequest before.work request).destination ∧
    result.state.dirty = true ∧
    result.state.work.qv = before.work.qv ∧ result.state.work.qe = before.work.qe ∧
    result.calls.map (fun call => (call.index, call.entry)) =
      F.walk before.transfer.physical.fibers.entries before.transfer.valid.backward
        (before.transfer.physical.fibers.heads request.original) ∧
    ∀ call ∈ result.calls,
      call.entry.key = request.original ∧
      TF.Delivered (canonicalRequest before.work request) result.state.transfer call ∧
      call.parameters.readout.valueRepresentative = result.state.work.qv ∧
      call.parameters.readout.effectRepresentative = result.state.work.qe

/-- The success hypothesis is the result of the whole executable composition,
including every pre-return insertion gate. The same-state connection and
captured-source coverage are conclusions of this theorem. -/
theorem bound_at_metadata (calls : Calls M) (inputs : TF.Inputs) (state : State M)
    (request : BoundRequest)
    (normal : (continueBound calls inputs state request).outcome = .originMetadata) :
    AtOriginMetadata state request (continueBound calls inputs state request) := by
  cases inserted : insert calls state request with
  | mk after actual outcome =>
    have named : actual = canonicalRequest state.work request := by
      simpa only [inserted] using insert_request calls state request
    have same : after.transfer = state.transfer := by
      simpa only [inserted] using insert_fibers_unchanged calls state request
    subst actual
    cases outcome with
    | failed failure => simp [continueBound, inserted] at normal
    | unscopedOwnerEmission => simp [continueBound, inserted] at normal
    | effectOwner antecedent => simp [continueBound, inserted] at normal
    | ready slot =>
      have physical := insert_ready calls state request slot (by simp only [inserted])
      simp only [inserted] at physical
      unfold continueBound at normal ⊢
      simp only [inserted] at normal ⊢
      try dsimp only at normal ⊢
      cases finished : (TF.transferBound (loopInputs after.work inputs)
          (canonicalRequest state.work request) after.transfer).outcome with
      | malformedCursor index => simp only [finished] at normal; cases normal
      | preparationFailure failure => simp only [finished] at normal; cases normal
      | transferFailure failure => simp only [finished] at normal; cases normal
      | complete =>
        have delivered := TF.bound_complete (loopInputs after.work inputs)
          (canonicalRequest state.work request) after.transfer finished
        refine ⟨slot, rfl, rfl, physical.1, physical.2.1, physical.2.2.1,
          physical.2.2.2, ?_, ?_⟩
        · simpa only [same, canonicalRequest] using delivered.1
        · intro call member
          obtain ⟨key, facts, exactKey⟩ := delivered.2 call member
          refine ⟨key, exactKey, ?_, ?_⟩
          · rw [facts.parameters]
            rfl
          · rw [facts.parameters]
            rfl

/-- An actual selected Bound with its actual memo hit enters the very same
insertion-and-loop computation. No arbitrary BoundRequest is supplied. -/
theorem selected_bound_execution (calls : Calls M) (inputs : TF.Inputs)
    (funds : W.Funding) (state : State M) (owner : Endpoint) (polarity : Polarity)
    (child : OriginalExtrusionWork.CopyKey) (original : RawBound)
    (popped : W.State) (copied : Endpoint)
    (selected : OriginalExtrusionWork.select state.work =
      some (.bound owner polarity child original, popped))
    (memo : popped.lookup child = some copied) :
    execute calls inputs funds state = continueBound calls inputs {state with work := popped}
      (W.boundRequest popped owner polarity copied original) := by
  rw [execute, OriginalExtrusionWork.selected_bound_dispatch funds state.work popped owner polarity
    child original copied selected memo]
  rfl

/-- Every entry of the head captured before insertion has an actual returned
call and a full child key at that SAME raw child ID in the destination fiber. -/
theorem every_captured_delivered (calls : Calls M) (inputs : TF.Inputs)
    (state : State M) (request : BoundRequest)
    (normal : (continueBound calls inputs state request).outcome = .originMetadata)
    (index : Nat) (entry : OriginalBoundFibers.Entry RawBound)
    (captured : (index, entry) ∈ F.walk state.transfer.physical.fibers.entries
      state.transfer.valid.backward (state.transfer.physical.fibers.heads request.original)) :
    ∃ call ∈ (continueBound calls inputs state request).calls,
      call.index = index ∧ call.entry = entry ∧
      TF.Delivered (canonicalRequest state.work request)
        (continueBound calls inputs state request).state.transfer call := by
  obtain ⟨slot, named, addressed, physical, dirty, values, effects, coverage, delivered⟩ :=
    bound_at_metadata calls inputs state request normal
  rw [← coverage] at captured
  obtain ⟨call, member, same⟩ := List.mem_map.mp captured
  refine ⟨call, member, congrArg Prod.fst same, congrArg Prod.snd same, ?_⟩
  exact (delivered call member).2.1

namespace Computed

/-- The entire pre-existing three-step row producer supplies the request.
`state.transfer` is the actual physical cut at that Bound request: the earlier
source-link owner is not re-extracted or asserted inert by this definition. -/
def rowExecution (calls : Calls M) (inputs : TF.Inputs) (state : State M)
    (caller : NativeValueStructure.Request) : Result M :=
  continueWork calls inputs state
    (W.runPrefix W.funded 3 (OriginalExtrusionWork.Computed.rowInput caller))

theorem row_execution_dispatch (calls : Calls M) (inputs : TF.Inputs) (state : State M)
    (caller : NativeValueStructure.Request) :
    rowExecution calls inputs state caller = continueBound calls inputs
      {state with work := OriginalExtrusionWork.Computed.rowBoundState caller}
      (OriginalExtrusionWork.Computed.rowBoundRequest caller) := by
  unfold rowExecution
  rw [(OriginalExtrusionWork.Computed.row_bound_produced caller).1]
  rfl

theorem row_execution_at_metadata (calls : Calls M) (inputs : TF.Inputs) (state : State M)
    (caller : NativeValueStructure.Request)
    (normal : (rowExecution calls inputs state caller).outcome = .originMetadata) :
    AtOriginMetadata {state with work := OriginalExtrusionWork.Computed.rowBoundState caller}
      (OriginalExtrusionWork.Computed.rowBoundRequest caller)
      (rowExecution calls inputs state caller) := by
  rw [row_execution_dispatch] at normal ⊢
  exact bound_at_metadata calls inputs _ _ normal

/-- A concrete metadata readout trace. Raw evidence IDs are opaque observed
outputs; the executable relation IDs below are generated by Native.call. -/
def goodCalls : Calls Nat where
  snapshot := fun m _ => ⟨m + 1, .ok 0⟩
  admission := fun m _ => ⟨m + 1, .ok 0⟩
  reserveEmission := fun m => ⟨m + 1, .ok ()⟩
  journal := fun m _ => ⟨m + 1, .ok ()⟩
  capacity := fun m _ => ⟨m + 1, .ok ()⟩
  accounting := fun m _ _ => m + 1
  emission := fun m _ _ _ => (m + 1, 0)
  sample := fun m => ⟨m + 1, .ok ()⟩

def sampleFailure : Calls Nat :=
  {goodCalls with sample := fun m => ⟨m + 1, .error 17⟩}

def resources : OriginalBoundFibers.PublicationResources :=
  ⟨{contextCount := 1}, true, true, {}, true⟩

def empty : TF.State :=
  ⟨⟨{}, {}⟩, OriginalBoundFibers.valid_empty, .initial⟩

/-- Actual raw interner and linked attach, with formation/history derived
from that computation. No arbitrary raw relation identity is inserted. -/
def seed (state : TF.State) (bound : RawBound) (key : Key) : TF.State where
  physical := (OriginalBoundFibers.publish state.physical state.valid resources bound key).1
  valid := OriginalBoundFibers.publish_valid state.physical state.valid resources bound key
  history := by
    rw [OriginalBoundFibers.publish_native]
    exact .commit state.history (.call (.nil _) resources.interner key)

def original : RawBound := ⟨.value (.row 0), .negative, .value (.row 1)⟩
def destination : RawBound := ⟨.value (.row 2), .negative, .value (.row 1)⟩
def sourceLink : RawBound := ⟨.value (.row 0), .positive, .value (.row 2)⟩

def firstKey : Key :=
  ⟨.value (.row 0) (.row 1), 0, some 42, ⟨0, some ⟨3, 4, 700, 5, 6⟩⟩⟩
def secondKey : Key :=
  ⟨.value (.row 0) (.row 1), 1, some 43, ⟨0, some ⟨7, 8, 701, 9, 10⟩⟩⟩
def linkKey : Key := ⟨.value (.row 2) (.row 0), 0, some 44, ⟨0, none⟩⟩

def firstSource : TF.State := seed empty original firstKey
def bothSources : TF.State := seed firstSource original secondKey
def sourceState : TF.State := seed bothSources sourceLink linkKey

def inputs : TF.Inputs := fun _ _ _ =>
  ⟨true,
    ⟨id, id, fun parent => parent == 1, fun _ => some 0⟩,
    resources⟩

/-- This is a composed local cut, including the earlier source-link fiber.
It is not a theorem extracting that cut from an entire Rust source session. -/
def rowState (caller : NativeValueStructure.Request) : State Nat :=
  {work := OriginalExtrusionWork.Computed.rowBoundState caller,
   transfer := sourceState, bookkeeping := 0}

def successful (caller : NativeValueStructure.Request) : Result Nat :=
  rowExecution goodCalls inputs (rowState caller) caller

def sampleFailed (caller : NativeValueStructure.Request) : Result Nat :=
  rowExecution sampleFailure inputs (rowState caller) caller

def exampleCaller : NativeValueStructure.Request :=
  ⟨.row 0, .row 1, 1, some 70, 0, some ⟨80, 81, 700, 82, 83⟩⟩

def firstChild : Key := {firstKey with pair := .value (.row 2) (.row 1)}
def secondChild : Key := {secondKey with pair := .value (.row 2) (.row 1), context := 0}

theorem sources_generated :
    sourceState.physical.native.store.readback 0 = some firstKey ∧
    sourceState.physical.native.store.readback 1 = some secondKey ∧
    sourceState.physical.native.store.readback 2 = some linkKey ∧
    F.fibers sourceState.physical.fibers sourceState.valid original = [1, 0] ∧
    F.fibers sourceState.physical.fibers sourceState.valid sourceLink = [2] := by
  decide +kernel

theorem row_physical_and_order (caller : NativeValueStructure.Request) :
    ((successful caller).state.work.values[2]?).map (fun row => row.upperRows) = some [1] ∧
    (successful caller).state.dirty = true ∧
    (successful caller).state.bookkeeping = 8 ∧
    (successful caller).state.trace =
      [.snapshot, .admission, .reserveEmission, .journal, .capacity,
       .append, .accounting, .readback, .capture, .emission, .sample] ∧
    (successful caller).request = some (OriginalExtrusionWork.Computed.rowBoundRequest caller) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem row_first_loop_complete :
    (successful exampleCaller).outcome = .originMetadata := by
  decide +kernel

theorem row_exact_children :
    (successful exampleCaller).calls.map (fun call => (call.entry.relation, call.child)) = [(1, 3), (0, 4)] ∧
    (successful exampleCaller).state.transfer.physical.native.store.readback 3 = some secondChild ∧
    (successful exampleCaller).state.transfer.physical.native.store.readback 4 = some firstChild ∧
    F.fibers (successful exampleCaller).state.transfer.physical.fibers
      (successful exampleCaller).state.transfer.valid destination = [4, 3] := by
  decide +kernel

theorem row_all_captured :
    AtOriginMetadata (rowState exampleCaller) (OriginalExtrusionWork.Computed.rowBoundRequest exampleCaller)
      (successful exampleCaller) := by
  exact row_execution_at_metadata goodCalls inputs (rowState exampleCaller) exampleCaller
    row_first_loop_complete

/-- Failure after append, physical readback, capture, dirty and evidence
emission keeps every one of those writes; the executable loop has not run. -/
theorem sample_failure_keeps_append (caller : NativeValueStructure.Request) :
    (sampleFailed caller).outcome = .insertionFailed ∧
    ((sampleFailed caller).state.work.values[2]?).map (fun row => row.upperRows) = some [1] ∧
    (sampleFailed caller).state.dirty = true ∧
    (sampleFailed caller).state.bookkeeping = 8 ∧
    (sampleFailed caller).state.emissions.map (fun emitted => (emitted.id, emitted.bound)) =
      [(0, destination)] ∧
    (sampleFailed caller).state.transfer = sourceState ∧
    (sampleFailed caller).calls = [] ∧
    ((sampleFailed caller).insertion.map (fun result => result.outcome)) =
      some (.failed (.native .sample 17)) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A second independent failure cut, now AFTER actual raw interning and
attachment in the first transfer body. The failed body is not logged as a
completed call and the later captured parent has not been visited. -/
def failingLoopInputs : TF.Inputs := fun physical index parent =>
  let readout := inputs physical index parent
  {readout with resources := {readout.resources with sample := false}}

def fiberFailed : Result Nat :=
  rowExecution goodCalls failingLoopInputs (rowState exampleCaller) exampleCaller

theorem fiber_sample_failure_keeps_partial :
    fiberFailed.outcome = .fiberFailure (.transferFailure (.published (.sampleFailure 3))) ∧
    (fiberFailed.state.work.values[2]?).map (fun row => row.upperRows) = some [1] ∧
    fiberFailed.state.dirty = true ∧
    fiberFailed.state.transfer.physical.native.store.readback 3 = some secondChild ∧
    fiberFailed.state.transfer.physical.native.store.readback 4 = none ∧
    F.fibers fiberFailed.state.transfer.physical.fibers
      fiberFailed.state.transfer.valid destination = [3] ∧
    fiberFailed.calls.length = 0 := by
  decide +kernel

end Computed

end YulangClosure.OriginalBoundWorkExecution
