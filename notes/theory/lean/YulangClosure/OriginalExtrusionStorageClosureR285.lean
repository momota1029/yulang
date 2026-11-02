import YulangClosure.OriginalExtrusionCaptureValidityR284

/-! Storage-reference closure for the existing operation-local model.  This
checks published row/term/memo/queue/parent/port references through R283,
incidences through R284, and every published Effect view tail.  It does not
assert native extraction or source reachability. -/
namespace YulangClosure.OriginalExtrusionStorageClosureR285

open OriginalExtrusionWork
open OriginalExtrusionRowValidityR283
open OriginalExtrusionCaptureValidityR284

/-- A published Effect view tail may be read later by `visitStructure`. -/
def ViewTailsValid (s : State) : Prop :=
  ∀ view tail, s.views view = some (some tail) →
    tail < s.effects.length ∧ s.qe tail < s.effects.length

/-- R283 checks row leaves and structural children. A stored Value leaf can
also name a structural term; `readValue` returns that endpoint. -/
def LeafRefsValid (s : State) : Prop :=
  ∀ entry ∈ s.terms, match entry.2.cell with
    | .valueLeaf endpoint =>
        OriginalInferenceTerminationResolution.valueTerm endpoint = none ∧
        ValueValid s endpoint ∧ ValueValid s (endpoint.rename s.qv)
    | .effectLeaf endpoint => EffectValid s endpoint ∧
        EffectValid s (NativeMergeExpansion.renameEndpoint s.qe endpoint)
    | .structure _ => True

/-- The model consumes view identities when visiting a rigid Effect endpoint.
Published tails are checked separately. -/
def EffectViewRefValid (s : State) : NativeMergeExpansion.Endpoint → Prop
  | .allowance view | .support view | .annotationMember view _ =>
      s.views view ≠ none
  | _ => True

def EndpointViewRefValid (s : State) : Endpoint → Prop
  | .value _ => True
  | .effect endpoint => EffectViewRefValid s endpoint

def KeyViewRefValid (s : State) (key : CopyKey) : Prop :=
  EndpointViewRefValid s key.endpoint

def BoundViewRefValid (s : State) (bound : RawBound) : Prop :=
  EndpointViewRefValid s bound.owner ∧ EndpointViewRefValid s bound.endpoint

def WorkViewRefValid (s : State) : Work → Prop
  | .visit key => KeyViewRefValid s key
  | .function key children _ =>
      KeyViewRefValid s key ∧ ∀ child ∈ children, KeyViewRefValid s child
  | .tuple key _ _ | .record key _ _ | .variant key _ _ => KeyViewRefValid s key
  | .effectView key view child =>
      KeyViewRefValid s key ∧ s.views view ≠ none ∧ KeyViewRefValid s child
  | .bound owner _ child source =>
      EndpointViewRefValid s owner ∧ KeyViewRefValid s child ∧ BoundViewRefValid s source
  | .incomingAllowance _ view source original =>
      s.views view ≠ none ∧ KeyViewRefValid s source ∧ BoundViewRefValid s original

/-- Every model-owned place carrying an Effect-view identity. The operation's
external `caller` payload is copied but never dereferenced by this model. -/
def ViewRefsValid (s : State) : Prop :=
  EndpointViewRefValid s s.operation.initial ∧
  (∀ row ∈ s.effects, (∀ e ∈ row.lowerAtoms, EffectViewRefValid s e) ∧
    (∀ e ∈ row.upperAtoms, EffectViewRefValid s e)) ∧
  (∀ entry ∈ s.terms, match entry.2.cell with
    | .effectLeaf endpoint => EffectViewRefValid s endpoint
    | _ => True) ∧
  (∀ id, ∀ incidence ∈ s.captures id, s.views incidence.view ≠ none) ∧
  (∀ key endpoint, s.rows key = some endpoint →
    KeyViewRefValid s key ∧ EndpointViewRefValid s endpoint) ∧
  (∀ key endpoint, s.structureMemo key = some endpoint →
    KeyViewRefValid s key ∧ EndpointViewRefValid s endpoint) ∧
  (∀ item ∈ s.work, WorkViewRefValid s item) ∧
  (∀ item ∈ s.pendingBounds, WorkViewRefValid s item) ∧
  (∀ port ∈ s.tuplePorts, KeyViewRefValid s port.1) ∧
  (∀ parent ∈ s.parents, EndpointViewRefValid s parent.copy ∧
    EndpointViewRefValid s parent.parent ∧
    EndpointViewRefValid s parent.operation.initial)

/-- A nonempty capture bucket is indexed by a published Effect tail row. -/
def CaptureBucketsValid (s : State) : Prop :=
  ∀ id, s.captures id ≠ [] → id < s.effects.length ∧
    s.qe id < s.effects.length

/-- Row kinds do not cross the Value/Effect boundary when a memo or retained
parent supplies a copied endpoint. -/
def SameKind : Endpoint → Endpoint → Prop
  | .value _, .value _ => True
  | .effect _, .effect _ => True
  | _, _ => False

def MemoKindsValid (s : State) : Prop :=
  (∀ key endpoint, s.rows key = some endpoint → SameKind key.endpoint endpoint) ∧
  (∀ key endpoint, s.structureMemo key = some endpoint → SameKind key.endpoint endpoint)

def ParentKindsValid (s : State) : Prop :=
  ∀ parent ∈ s.parents, SameKind parent.parent parent.copy

/-- Structural closure of the model's stored references. `RowsValid` covers
both raw references and the kind-separated canonical maps. -/
def StorageClosed (s : State) : Prop :=
  RowsValid s ∧ CapturesValid s ∧ ViewTailsValid s ∧
    LeafRefsValid s ∧ ViewRefsValid s ∧ CaptureBucketsValid s ∧
    MemoKindsValid s ∧ ParentKindsValid s

theorem storage_implies_capture_complete (s : State)
    (h : StorageClosed s) : CaptureComplete s := ⟨h.1, h.2.1⟩

theorem capture_gap_not_storage (caller : NativeValueStructure.Request) :
    ¬ StorageClosed (captureGap caller) := by
  intro h
  exact capture_gap_excluded caller (storage_implies_capture_complete _ h)

theorem view_tail_gap_not_storage : ¬ StorageClosed viewTailGap := by
  intro h
  have ht := h.2.2.1 7 99 (by decide)
  simp [viewTailGap, OriginalExtrusionWork.Computed.rowInput] at ht

theorem computed_rowInput_storage (caller : NativeValueStructure.Request) :
    StorageClosed (Computed.rowInput caller) := by
  refine ⟨(computed_rowInput_capture_complete caller).1,
    (computed_rowInput_capture_complete caller).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ViewTailsValid, Computed.rowInput]
  · simp [LeafRefsValid, Computed.rowInput]
  · simp [ViewRefsValid, Computed.rowInput, EndpointViewRefValid,
      KeyViewRefValid, WorkViewRefValid]
  · simp [CaptureBucketsValid, Computed.rowInput]
  · simp [MemoKindsValid, Computed.rowInput]
  · simp [ParentKindsValid, Computed.rowInput]

/-- A row allocation extends the selected vector and keeps a valid old
capture source inside its kind-separated canonical map. -/
theorem capture_source_transfer_allocate (s : State) (key : CopyKey) (source : Nat)
    (h : CaptureSourceValid s source) :
    CaptureSourceValid (s.allocate key) source :=
  capture_source_valid_allocate s key source h

theorem value_canonical_old_after_allocate (s : State) (key : CopyKey) (id : Nat)
    (h : id < s.values.length) : (s.allocate key).qv id = s.qv id := by
  cases key with
  | mk endpoint polarity target =>
    cases endpoint with
    | value endpoint => simp [State.allocate, Nat.ne_of_lt h]
    | effect endpoint => rfl

theorem effect_canonical_old_after_allocate (s : State) (key : CopyKey) (id : Nat)
    (h : id < s.effects.length) : (s.allocate key).qe id = s.qe id := by
  cases key with
  | mk endpoint polarity target =>
    cases endpoint with
    | value endpoint => rfl
    | effect endpoint => simp [State.allocate, Nat.ne_of_lt h]

theorem capture_buckets_transfer_allocate (s : State) (key : CopyKey)
    (h : CaptureBucketsValid s) : CaptureBucketsValid (s.allocate key) := by
  intro id nonempty
  cases key with
  | mk endpoint polarity target =>
    cases endpoint with
    | value endpoint =>
      have old : s.captures id ≠ [] := by simpa [State.allocate] using nonempty
      simpa [State.allocate] using h id old
    | effect endpoint =>
      have old : s.captures id ≠ [] := by simpa [State.allocate] using nonempty
      have bounds := h id old
      simp only [State.allocate, List.length_append, List.length_singleton, Nat.add_one]
      constructor
      · omega
      · have hne : id ≠ s.effects.length := by omega
        simp [hne]
        omega

/-- The actual memo update preserves kind separation if the published image
has the same kind as its key. -/
theorem memo_kind_transfer_put (memo : Memo) (key : CopyKey) (endpoint : Endpoint)
    (hold : ∀ query image, memo query = some image →
      SameKind query.endpoint image)
    (hnew : SameKind key.endpoint endpoint) :
    ∀ query image, memoPut memo key endpoint query = some image →
      SameKind query.endpoint image := by
  intro query image hlookup
  by_cases hq : query = key
  · subst query
    simp [memoPut] at hlookup
    cases hlookup
    exact hnew
  · have old : memo query = some image := by simpa [memoPut, hq] using hlookup
    exact hold query image old

/-- Queue insertion changes neither published views nor their canonical map. -/
theorem view_tails_transfer_pushed (s : State) (pending : Bool) (items : List Work)
    (h : ViewTailsValid s) : ViewTailsValid (pushed pending items s) := by
  cases pending <;> simpa [ViewTailsValid, pushed] using h

theorem leaf_refs_transfer_pushed (s : State) (pending : Bool) (items : List Work)
    (h : LeafRefsValid s) : LeafRefsValid (pushed pending items s) := by
  cases pending <;> simpa [LeafRefsValid, pushed, State.storedTerm,
    ValueValid, EffectValid] using h

/-- Publication through either memo leaves all published views unchanged. -/
theorem view_tails_transfer_memo (s : State) (row : Bool) (key : CopyKey)
    (endpoint : Endpoint) (h : ViewTailsValid s) :
    ViewTailsValid {s with
      rows := if row then memoPut s.rows key endpoint else s.rows,
      structureMemo := if row then s.structureMemo else memoPut s.structureMemo key endpoint} := by
  cases row <;> simpa [ViewTailsValid] using h

/-- Existing valid view tails remain valid after either kind of row allocation. -/
theorem view_tails_transfer_allocate (s : State) (key : CopyKey)
    (h : ViewTailsValid s) : ViewTailsValid (s.allocate key) := by
  intro view tail hp
  cases key with
  | mk endpoint polarity target =>
    cases endpoint with
    | value endpoint => simpa [State.allocate, ViewTailsValid] using h view tail hp
    | effect endpoint =>
      have old := h view tail hp
      simp only [State.allocate, List.length_append, List.length_singleton, Nat.add_one]
      constructor
      · omega
      · have hne : tail ≠ s.effects.length := by omega
        simp [hne]
        omega

/-- Pushing a finite work batch transfers the view-reference obligation
exactly when every newly queued item already satisfies it. -/
theorem queued_view_refs_pushed (s : State) (pending : Bool) (items : List Work)
    (hwork : ∀ item ∈ s.work, WorkViewRefValid s item)
    (hpending : ∀ item ∈ s.pendingBounds, WorkViewRefValid s item)
    (hitems : ∀ item ∈ items, WorkViewRefValid s item) :
    (∀ item ∈ (pushed pending items s).work,
      WorkViewRefValid (pushed pending items s) item) ∧
    (∀ item ∈ (pushed pending items s).pendingBounds,
      WorkViewRefValid (pushed pending items s) item) := by
  cases pending
  · constructor
    · intro item hm
      simp only [pushed] at hm ⊢
      have : item ∈ items.reverse ∨ item ∈ s.work := by
        simpa using hm
      rcases this with hi | ho
      · simpa [WorkViewRefValid, EffectViewRefValid,
          EndpointViewRefValid, KeyViewRefValid, BoundViewRefValid, pushed]
          using hitems item (by simpa using hi)
      · simpa [WorkViewRefValid, EffectViewRefValid,
          EndpointViewRefValid, KeyViewRefValid, BoundViewRefValid, pushed]
          using hwork item ho
    · intro item hm
      simpa [WorkViewRefValid, EffectViewRefValid,
        EndpointViewRefValid, KeyViewRefValid, BoundViewRefValid, pushed]
        using hpending item hm
  · constructor
    · intro item hm
      simpa [WorkViewRefValid, EffectViewRefValid,
        EndpointViewRefValid, KeyViewRefValid, BoundViewRefValid, pushed]
        using hwork item hm
    · intro item hm
      simp only [pushed] at hm ⊢
      have : item ∈ items.reverse ∨ item ∈ s.pendingBounds := by
        simpa using hm
      rcases this with hi | ho
      · simpa [WorkViewRefValid, EffectViewRefValid,
          EndpointViewRefValid, KeyViewRefValid, BoundViewRefValid, pushed]
          using hitems item (by simpa using hi)
      · simpa [WorkViewRefValid, EffectViewRefValid,
          EndpointViewRefValid, KeyViewRefValid, BoundViewRefValid, pushed]
          using hpending item ho

/-- The three transfer-only Work constructors either hand off an external
request or fail before a local store write. The selected queue item was
already removed by `select`; this lemma is about `perform` itself. -/
theorem bound_perform_retains_state (funds : Funding) (s : State)
    (owner : Endpoint) (p : NativeMergeExpansion.Polarity)
    (child : CopyKey) (source : RawBound) :
    resultState (perform funds s (.bound owner p child source)) = s := by
  simp [perform]
  split <;> rfl

theorem incoming_perform_retains_state (funds : Funding) (s : State)
    (tail view : Nat) (source : CopyKey) (original : RawBound) :
    resultState (perform funds s (.incomingAllowance tail view source original)) = s := by
  simp [perform]
  split <;> rfl

theorem effect_view_perform_retains_state (funds : Funding) (s : State)
    (key : CopyKey) (view : Nat) (child : CopyKey) :
    resultState (perform funds s (.effectView key view child)) = s := by
  simp [perform]
  split <;> rfl

/-- The complete caller is retained for native handoff but is opaque to the
local model's row reads. Requiring its endpoints to be present at the computed
initial state conflicts with `rowInput`'s arbitrary-caller quantifier. -/
def CallerRowsValid (s : State) : Prop :=
  ValueValid s s.operation.caller.lower ∧
  ValueValid s s.operation.caller.upper

def invalidCaller : NativeValueStructure.Request :=
  ⟨.row 99, .row 0, 0, none, 0, none⟩

theorem computed_rowInput_invalid_caller :
    ¬ CallerRowsValid (Computed.rowInput invalidCaller) := by
  simp [CallerRowsValid, Computed.rowInput, invalidCaller, ValueValid]

theorem no_universal_computed_input_with_caller
    (predicate : State → Prop)
    (coversCaller : ∀ s, predicate s → CallerRowsValid s) :
    ¬ (∀ caller : NativeValueStructure.Request,
      predicate (Computed.rowInput caller)) := by
  intro allCallers
  exact computed_rowInput_invalid_caller
    (coversCaller _ (allCallers invalidCaller))


end YulangClosure.OriginalExtrusionStorageClosureR285
