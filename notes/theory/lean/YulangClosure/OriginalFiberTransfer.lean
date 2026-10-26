import YulangClosure.OriginalExtrusionFibers

/-!
The first, executable-fiber loop of candidate_transfer_bound_origins. It
captures the stored head once and reads the next pointer before each physical
transfer. Successful calls are recorded by their actual raw source and child
identities. Snapshot/evidence and representative readouts remain explicit
native extraction inputs; the later origin-metadata loop is a separate owner.
-/
namespace YulangClosure.OriginalFiberTransfer

open OriginalExtrusionWork (RawBound BoundRequest)
open NativeValuePorts (Key)
namespace F
export OriginalBoundFibers (Physical Store Valid Entry Run fibers walk cursorRank)
end F
namespace T
export OriginalExtrusionFibers (Readout Outcome transfer transfer_valid transfer_history
  transfer_fiber_run transfer_native_run transferred_fiber_exact)
end T

structure State where
  physical : F.Physical RawBound
  valid : F.Valid physical.fibers
  history : NativeRelationInterner.NativeHistory physical.native

/-- These are the observed results/readouts of the named native body calls,
not a predicate assuming successful transport or target membership. -/
structure Parameters where
  snapshot : Bool
  readout : T.Readout
  resources : OriginalBoundFibers.PublicationResources

abbrev Inputs := F.Physical RawBound → Nat → Nat → Parameters

def advanced (state : State) (parameters : Parameters) (request : BoundRequest)
    (parent : Nat) : State :=
  ⟨(T.transfer state.physical state.valid parameters.readout parameters.resources request parent).1,
    T.transfer_valid state.physical state.valid parameters.readout parameters.resources request parent,
    T.transfer_history state.physical state.valid state.history parameters.readout
      parameters.resources request parent⟩

structure Call where
  index : Nat
  entry : F.Entry RawBound
  before : State
  parameters : Parameters
  child : Nat

inductive PreparationFailure where
  | bound (failure : OriginalExtrusionFibers.Failure)
  | snapshot
  deriving DecidableEq, Repr

/-- Native bound_pair/canonicalization precedes evidence snapshot interning.
The kind-violation branch represents the native invariant trap, not a
successful snapshot or a silently admitted cross-kind bound. -/
def prepare (request : BoundRequest) (parameters : Parameters) : Except PreparationFailure Unit :=
  match OriginalExtrusionFibers.boundPair request.destination with
  | .error failure => .error (.bound failure)
  | .ok _ => if parameters.snapshot = false then .error .snapshot else .ok ()

theorem prepare_snapshot (request : BoundRequest) (parameters : Parameters)
    (computed : prepare request parameters = .ok ()) : parameters.snapshot ≠ false := by
  intro snapshot
  cases paired : OriginalExtrusionFibers.boundPair request.destination with
  | error failure => simp [prepare, paired] at computed
  | ok pair => simp [prepare, paired, snapshot] at computed

inductive Outcome where
  | complete
  | malformedCursor (index : Nat)
  | preparationFailure (failure : PreparationFailure)
  | transferFailure (outcome : T.Outcome)
  deriving DecidableEq, Repr

structure Result where
  state : State
  calls : List Call
  outcome : Outcome

def completed : T.Outcome → Option Nat
  | .published (.complete child) => some child
  | _ => none

theorem completed_exact (outcome : T.Outcome) (child : Nat) :
    completed outcome = some child ↔ outcome = .published (.complete child) := by
  cases outcome with
  | keyFailure failure => simp [completed]
  | published outcome => cases outcome <;> simp [completed]

/-- Exact linked control of the first native loop, including early errors.
The `none` branch is its own cut, before any origin-metadata processing.
There is no iteration fuel: the next pointer is strictly older in the same
physical table even when a successful body grows that table. -/
def loop (inputs : Inputs) (request : BoundRequest) (state : State)
    (cursor : Option Nat) : Result :=
  match cursor with
  | none => ⟨state, [], .complete⟩
  | some index =>
    match _found : state.physical.fibers.entries[index]? with
    | none => ⟨state, [], .malformedCursor index⟩
    | some entry =>
      let next := entry.previous
      let parameters := inputs state.physical index entry.relation
      match prepare request parameters with
      | .error failure => ⟨state, [], .preparationFailure failure⟩
      | .ok () =>
        let called := T.transfer state.physical state.valid parameters.readout
          parameters.resources request entry.relation
        let after := advanced state parameters request entry.relation
        match completed called.2 with
        | some child =>
          let rest := loop inputs request after next
          ⟨rest.state, ⟨index, entry, state, parameters, child⟩ :: rest.calls, rest.outcome⟩
        | none => ⟨after, [], .transferFailure called.2⟩
termination_by F.cursorRank cursor
decreasing_by
  cases previous : entry.previous with
  | none => simp [F.cursorRank]
  | some old =>
    have earlier := state.valid.backward index entry _found old previous
    simp only [F.cursorRank]
    omega

def transferBound (inputs : Inputs) (request : BoundRequest) (state : State) : Result :=
  loop inputs request state (state.physical.fibers.heads request.original)

theorem fiber_run_trans {first middle last : F.Store RawBound}
    (before : F.Run first middle) (after : F.Run middle last) : F.Run first last := by
  induction after with
  | nil => exact before
  | call _ valid resources key relation ih => exact .call ih valid resources key relation

theorem native_run_trans {first middle last : NativeRelationInterner.Native}
    (before : NativeRelationInterner.NativeRun first middle)
    (after : NativeRelationInterner.NativeRun middle last) :
    NativeRelationInterner.NativeRun first last := by
  induction after with
  | nil => exact before
  | inventory _ amount maximum fits bounded ih => exact .inventory ih amount maximum fits bounded
  | call _ resources key ih => exact .call ih resources key

theorem loop_footprints (inputs : Inputs) (request : BoundRequest) (state : State)
    (cursor : Option Nat) :
    F.Run state.physical.fibers (loop inputs request state cursor).state.physical.fibers ∧
      NativeRelationInterner.NativeRun state.physical.native
        (loop inputs request state cursor).state.physical.native := by
  cases cursor with
  | none =>
    rw [loop]
    exact ⟨.nil _, .nil _⟩
  | some index =>
    rw [loop]
    cases found : state.physical.fibers.entries[index]? with
    | none =>
      simp only
      exact ⟨.nil _, .nil _⟩
    | some entry =>
      simp only
      cases preparation : prepare request (inputs state.physical index entry.relation) with
      | error failure =>
        simp only
        exact ⟨.nil _, .nil _⟩
      | ok accepted =>
        cases accepted
        simp only
        let parameters := inputs state.physical index entry.relation
        have fiber := T.transfer_fiber_run state.physical state.valid
          parameters.readout parameters.resources request entry.relation
        have native := T.transfer_native_run state.physical state.valid
          parameters.readout parameters.resources request entry.relation
        cases called : completed (T.transfer state.physical state.valid
            parameters.readout parameters.resources request entry.relation).2 with
        | none =>
          simp only
          exact ⟨fiber, native⟩
        | some child =>
          simp only
          have rest := loop_footprints inputs request
            (advanced state parameters request entry.relation) entry.previous
          exact ⟨fiber_run_trans fiber rest.1, native_run_trans native rest.2⟩
termination_by F.cursorRank cursor
decreasing_by
  subst cursor
  cases previous : entry.previous with
  | none => simp [F.cursorRank]
  | some old =>
    have earlier := state.valid.backward index entry found old previous
    simp only [F.cursorRank]
    omega

theorem loop_old_readback (inputs : Inputs) (request : BoundRequest) (state : State)
    (cursor : Option Nat) (relation : Nat) (key : Key)
    (old : state.physical.native.store.readback relation = some key) :
    (loop inputs request state cursor).state.physical.native.store.readback relation = some key := by
  obtain ⟨coherent, projected⟩ := NativeRelationInterner.native_history_refinement state.history
  exact NativeRelationInterner.old_relation_readback projected
    (NativeRelationInterner.native_run_refinement
      (loop_footprints inputs request state cursor).2 coherent).2 old

theorem loop_preserves_fiber (inputs : Inputs) (request : BoundRequest) (state : State)
    (cursor : Option Nat) (bound : RawBound) (relation : Nat)
    (old : relation ∈ F.fibers state.physical.fibers state.valid bound) :
    relation ∈ F.fibers (loop inputs request state cursor).state.physical.fibers
      (loop inputs request state cursor).state.valid bound :=
  OriginalBoundFibers.run_preserves_fiber
    (loop_footprints inputs request state cursor).1 state.valid bound relation old

theorem loop_captured_cursor (inputs : Inputs) (request : BoundRequest) (state : State)
    (cursor captured : Option Nat)
    (bounded : ∀ index, captured = some index → index < state.physical.fibers.entries.length) :
    F.walk (loop inputs request state cursor).state.physical.fibers.entries
      (loop inputs request state cursor).state.valid.backward captured =
      F.walk state.physical.fibers.entries state.valid.backward captured :=
  OriginalBoundFibers.run_captured_cursor
    (loop_footprints inputs request state cursor).1 state.valid captured bounded

/-- A normal first-loop result processes precisely the original captured
entries, in their physical linked order. The live source head is never read
again, even when the target is that same source bound. -/
theorem loop_complete_entries (inputs : Inputs) (request : BoundRequest) (state : State)
    (cursor : Option Nat) (normal : (loop inputs request state cursor).outcome = .complete) :
    (loop inputs request state cursor).calls.map (fun call => (call.index, call.entry)) =
      F.walk state.physical.fibers.entries state.valid.backward cursor := by
  cases cursor with
  | none =>
    rw [loop, OriginalBoundFibers.walk_none]
    rfl
  | some index =>
    rw [loop] at normal ⊢
    generalize found : state.physical.fibers.entries[index]? = lookup at normal ⊢
    cases lookup with
    | none => cases normal
    | some entry =>
      simp only at normal ⊢
      let parameters := inputs state.physical index entry.relation
      generalize prepared : prepare request parameters = preparation at normal ⊢
      cases preparation with
      | error failure => cases normal
      | ok accepted =>
        cases accepted
        simp only at normal ⊢
        generalize called : completed (T.transfer state.physical state.valid
            parameters.readout parameters.resources request entry.relation).2 = result at normal ⊢
        cases result with
        | none => cases normal
        | some child =>
          simp only at normal ⊢
          have rest := loop_complete_entries inputs request
            (advanced state parameters request entry.relation) entry.previous normal
          have bounded : ∀ old, entry.previous = some old → old < state.physical.fibers.entries.length := by
            intro old previous
            exact Nat.lt_trans (state.valid.backward index entry found old previous)
              (List.getElem?_eq_some_iff.mp found).1
          have captured := OriginalBoundFibers.run_captured_cursor
            (T.transfer_fiber_run state.physical state.valid parameters.readout
              parameters.resources request entry.relation) state.valid entry.previous bounded
          rw [OriginalBoundFibers.walk_some _ _ found]
          change (index, entry) :: _ = (index, entry) :: _
          rw [rest]
          exact congrArg (List.cons (index, entry)) captured
termination_by F.cursorRank cursor
decreasing_by
  subst cursor
  cases previous : entry.previous with
  | none => simp [F.cursorRank]
  | some old =>
    have earlier := state.valid.backward index entry found old previous
    simp only [F.cursorRank]
    omega

/-- Facts extracted from a computed successful body call, together with the
actual forward suffix after that call. The loop theorem constructs all fields;
no caller supplies this certificate to the executable loop. -/
structure CallFacts (inputs : Inputs) (request : BoundRequest) (last : State) (call : Call) : Prop where
  found : call.before.physical.fibers.entries[call.index]? = some call.entry
  parameters : call.parameters = inputs call.before.physical call.index call.entry.relation
  snapshot : call.parameters.snapshot ≠ false
  normal : (T.transfer call.before.physical call.before.valid call.parameters.readout
    call.parameters.resources request call.entry.relation).2 = .published (.complete call.child)
  fibers : F.Run (advanced call.before call.parameters request call.entry.relation).physical.fibers
    last.physical.fibers
  native : NativeRelationInterner.NativeRun
    (advanced call.before call.parameters request call.entry.relation).physical.native last.physical.native

theorem loop_call_facts (inputs : Inputs) (request : BoundRequest) (state : State)
    (cursor : Option Nat) (call : Call)
    (member : call ∈ (loop inputs request state cursor).calls) :
    CallFacts inputs request (loop inputs request state cursor).state call := by
  cases cursor with
  | none =>
    rw [loop] at member
    cases member
  | some index =>
    rw [loop] at member ⊢
    generalize found : state.physical.fibers.entries[index]? = lookup at member ⊢
    cases lookup with
    | none => cases member
    | some entry =>
      simp only at member ⊢
      let parameters := inputs state.physical index entry.relation
      generalize prepared : prepare request parameters = preparation at member ⊢
      cases preparation with
      | error failure => cases member
      | ok accepted =>
        cases accepted
        simp only at member ⊢
        generalize called : completed (T.transfer state.physical state.valid
            parameters.readout parameters.resources request entry.relation).2 = result at member ⊢
        cases result with
        | none => cases member
        | some child =>
          simp only at member ⊢
          rcases List.mem_cons.mp member with rfl | later
          · have rest := loop_footprints inputs request
              (advanced state parameters request entry.relation) entry.previous
            exact ⟨found, rfl, prepare_snapshot request parameters prepared,
              (completed_exact _ child).mp called, rest.1, rest.2⟩
          · exact loop_call_facts inputs request
              (advanced state parameters request entry.relation) entry.previous call later
termination_by F.cursorRank cursor
decreasing_by
  subst cursor
  cases previous : entry.previous with
  | none => simp [F.cursorRank]
  | some old =>
    have earlier := state.valid.backward index entry found old previous
    simp only [F.cursorRank]
    omega

/-- The complete computed key survives at the SAME actual returned child ID,
and that ID is still present in the destination's physical fiber list. -/
def Delivered (request : BoundRequest) (last : State) (call : Call) : Prop :=
  ∃ source pair flow key,
    call.before.physical.native.store.readback call.entry.relation = some source ∧
    OriginalExtrusionFibers.boundPair request.destination = .ok pair ∧
    OriginalExtrusionFibers.remapFlow request.original request.destination source.flow = .ok flow ∧
    key = ⟨pair.rename call.parameters.readout.valueRepresentative
        call.parameters.readout.effectRepresentative,
      OriginalExtrusionFibers.postContext call.parameters.readout call.entry.relation source.context,
      source.sources, flow⟩ ∧
    NativeValuePorts.Allowed key ∧
    OriginalExtrusionFibers.metadata key.flow = OriginalExtrusionFibers.metadata source.flow ∧
    last.physical.native.store.readback call.child = some key ∧
    call.child ∈ F.fibers last.physical.fibers last.valid request.destination

theorem call_delivered {inputs : Inputs} {request : BoundRequest} {last : State} {call : Call}
    (facts : CallFacts inputs request last call) : Delivered request last call := by
  obtain ⟨source, pair, flow, key, stored, paired, mapped, shape, allowed, fields, readback, member⟩ :=
    T.transferred_fiber_exact call.before.physical call.before.valid call.before.history
      call.parameters.readout call.parameters.resources request call.entry.relation call.child facts.normal
  refine ⟨source, pair, flow, key, stored, paired, mapped, shape, allowed, fields, ?_, ?_⟩
  · obtain ⟨coherent, projected⟩ := NativeRelationInterner.native_history_refinement
      (advanced call.before call.parameters request call.entry.relation).history
    exact NativeRelationInterner.old_relation_readback projected
      (NativeRelationInterner.native_run_refinement facts.native coherent).2 readback
  · exact OriginalBoundFibers.run_preserves_fiber facts.fibers
      (advanced call.before call.parameters request call.entry.relation).valid
      request.destination call.child member

theorem loop_delivers (inputs : Inputs) (request : BoundRequest) (state : State)
    (cursor : Option Nat) (call : Call)
    (member : call ∈ (loop inputs request state cursor).calls) :
    Delivered request (loop inputs request state cursor).state call :=
  call_delivered (loop_call_facts inputs request state cursor call member)

/-- The whole first native fiber loop, with its head captured by this very
computation. Normal completion supplies every original entry and the fully
computed raw child key; source-list coverage is not an input hypothesis. -/
theorem bound_complete (inputs : Inputs) (request : BoundRequest) (state : State)
    (normal : (transferBound inputs request state).outcome = .complete) :
    (transferBound inputs request state).calls.map (fun call => (call.index, call.entry)) =
        F.walk state.physical.fibers.entries state.valid.backward
          (state.physical.fibers.heads request.original) ∧
      ∀ call ∈ (transferBound inputs request state).calls,
        call.entry.key = request.original ∧
        CallFacts inputs request (transferBound inputs request state).state call ∧
        Delivered request (transferBound inputs request state).state call := by
  have entries := loop_complete_entries inputs request state
    (state.physical.fibers.heads request.original) normal
  refine ⟨entries, ?_⟩
  intro call member
  have occurs : (call.index, call.entry) ∈ F.walk state.physical.fibers.entries
      state.valid.backward (state.physical.fibers.heads request.original) := by
    rw [← entries]
    exact List.mem_map.mpr ⟨call, member, rfl⟩
  have named := OriginalBoundFibers.walk_entry_key state.valid request.original
    (state.physical.fibers.heads request.original) (state.valid.heads request.original)
    (call.index, call.entry) occurs
  have facts := loop_call_facts inputs request state
    (state.physical.fibers.heads request.original) call member
  exact ⟨named.2, facts, call_delivered facts⟩

def Addressed (state : State) (cursor : Option Nat) : Prop :=
  ∀ index, cursor = some index →
    ∃ entry, state.physical.fibers.entries[index]? = some entry

/-- The explicit malformed-index branch cannot arise from an actual stored
head or its next pointers. This is derived from table formation and the exact
forward body footprint, not from normal completion of the whole loop. -/
theorem loop_addressed (inputs : Inputs) (request : BoundRequest) (state : State)
    (cursor : Option Nat) (addressed : Addressed state cursor) (bad : Nat) :
    (loop inputs request state cursor).outcome ≠ .malformedCursor bad := by
  cases cursor with
  | none =>
    rw [loop]
    intro impossible
    cases impossible
  | some index =>
    rw [loop]
    cases found : state.physical.fibers.entries[index]? with
    | none =>
      obtain ⟨entry, stored⟩ := addressed index rfl
      rw [found] at stored
      cases stored
    | some entry =>
      simp only
      let parameters := inputs state.physical index entry.relation
      cases prepared : prepare request parameters with
      | error failure =>
        simp only
        intro impossible
        cases impossible
      | ok accepted =>
        cases accepted
        simp only
        cases called : completed (T.transfer state.physical state.valid
            parameters.readout parameters.resources request entry.relation).2 with
        | none =>
          simp only
          intro impossible
          cases impossible
        | some child =>
          simp only
          apply loop_addressed inputs request
            (advanced state parameters request entry.relation) entry.previous _ bad
          intro previous link
          obtain ⟨old, stored, _⟩ := state.valid.links index entry previous found link
          refine ⟨old, ?_⟩
          exact OriginalBoundFibers.run_extends
            (T.transfer_fiber_run state.physical state.valid parameters.readout
              parameters.resources request entry.relation) previous old stored
termination_by F.cursorRank cursor
decreasing_by
  subst cursor
  cases previous : entry.previous with
  | none => simp [F.cursorRank]
  | some old =>
    have earlier := state.valid.backward index entry found old previous
    simp only [F.cursorRank]
    omega

theorem bound_cursor_formed (inputs : Inputs) (request : BoundRequest) (state : State) (bad : Nat) :
    (transferBound inputs request state).outcome ≠ .malformedCursor bad := by
  apply loop_addressed inputs request state _ _ bad
  intro index head
  obtain ⟨entry, found, _⟩ := state.valid.heads request.original index head
  exact ⟨entry, found⟩

end YulangClosure.OriginalFiberTransfer
