import YulangClosure.OriginalExtrusionWork

namespace YulangClosure.OriginalExtrusionRowValidityR283

open OriginalExtrusionWork
open OriginalInferenceTerminationResolution (Cell)

/-- A row reference is valid in the currently published physical stores. A
structural endpoint additionally needs its raw term label to be published. -/
def ValueValid (s : State) : NativeValuePorts.ValueEndpoint → Prop
  | .row id => id < s.values.length
  | .positiveFunction term | .negativeFunction term
  | .positiveRecord term | .negativeRecord term
  | .positiveVariant term | .negativeVariant term
  | .positiveTuple term _ | .negativeTuple term _ => s.storedTerm term ≠ none
  | _ => True

def EffectValid (s : State) : NativeMergeExpansion.Endpoint → Prop
  | .row id => id < s.effects.length
  | _ => True

def EndpointValid (s : State) : Endpoint → Prop
  | .value endpoint => ValueValid s endpoint
  | .effect endpoint => EffectValid s endpoint

def KeyValid (s : State) (key : CopyKey) : Prop := EndpointValid s key.endpoint

def BoundValid (s : State) (bound : RawBound) : Prop :=
  EndpointValid s bound.owner ∧ EndpointValid s bound.endpoint

def WorkValid (s : State) : Work → Prop
  | .visit key => KeyValid s key
  | .function key children originals =>
      KeyValid s key ∧ (∀ child ∈ children, KeyValid s child) ∧
      s.storedTerm originals.argument ≠ none ∧
      s.storedTerm originals.argumentEffect ≠ none ∧
      s.storedTerm originals.resultEffect ≠ none ∧
      s.storedTerm originals.result ≠ none
  | .tuple key _ _ | .record key _ _ | .variant key _ _ => KeyValid s key
  | .effectView key _ child => KeyValid s key ∧ KeyValid s child
  | .bound owner _ child source =>
      EndpointValid s owner ∧ KeyValid s child ∧ BoundValid s source
  | .incomingAllowance tail _ source original =>
      tail < s.effects.length ∧ KeyValid s source ∧ BoundValid s original

def ValueBoundsValid (s : State) (row : Bounds NativeValuePorts.ValueEndpoint) : Prop :=
  (∀ id ∈ row.lowerRows, id < s.values.length) ∧
  (∀ id ∈ row.upperRows, id < s.values.length) ∧
  (∀ endpoint ∈ row.lowerAtoms, ValueValid s endpoint) ∧
  (∀ endpoint ∈ row.upperAtoms, ValueValid s endpoint)

def EffectBoundsValid (s : State) (row : Bounds NativeMergeExpansion.Endpoint) : Prop :=
  (∀ id ∈ row.lowerRows, id < s.effects.length) ∧
  (∀ id ∈ row.upperRows, id < s.effects.length) ∧
  (∀ endpoint ∈ row.lowerAtoms, EffectValid s endpoint) ∧
  (∀ endpoint ∈ row.upperAtoms, EffectValid s endpoint)

def CellValid (s : State) (cell : StoredCell) : Prop :=
  (∀ row ∈ cell.cell.rows, match row with
    | .value id => id < s.values.length
    | .effect id => id < s.effects.length) ∧
  (∀ term ∈ cell.cell.children, s.storedTerm term ≠ none)

def ParentValid (s : State) (parent : Parent) : Prop :=
  EndpointValid s parent.copy ∧ EndpointValid s parent.parent ∧
  EndpointValid s parent.operation.initial

/-- Candidate whole-state row-reference invariant. It checks canonical
representatives, all published stores and cells, memo keys/images, queued Work
and retained parents. Capture incidences are intentionally outside this
candidate: the counterexample below tests whether that omission is sound. -/
def RowsValid (s : State) : Prop :=
  EndpointValid s s.operation.initial ∧
  (∀ id, id < s.values.length → s.qv id < s.values.length) ∧
  (∀ id, id < s.effects.length → s.qe id < s.effects.length) ∧
  (∀ row ∈ s.values, ValueBoundsValid s row) ∧
  (∀ row ∈ s.effects, EffectBoundsValid s row) ∧
  (∀ entry ∈ s.terms, CellValid s entry.2) ∧
  (∀ key endpoint, s.rows key = some endpoint → KeyValid s key ∧ EndpointValid s endpoint) ∧
  (∀ key endpoint, s.structureMemo key = some endpoint →
    KeyValid s key ∧ EndpointValid s endpoint) ∧
  (∀ item ∈ s.work, WorkValid s item) ∧
  (∀ item ∈ s.pendingBounds, WorkValid s item) ∧
  (∀ port ∈ s.tuplePorts, KeyValid s port.1 ∧ s.storedTerm port.2 ≠ none) ∧
  (∀ parent ∈ s.parents, ParentValid s parent) ∧
  (∀ index ∈ s.pendingParents, index < s.parents.length)

/-- All three outcomes retain their actual state, including external yield
and failure after partial publication. -/
def resultState : Result → State
  | .next s => s
  | .external s _ => s
  | .failed s _ => s

theorem resultState_next (s : State) : resultState (.next s) = s := rfl
theorem resultState_external (s : State) (call : External) :
    resultState (.external s call) = s := rfl
theorem resultState_failed (s : State) (error : Failure) :
    resultState (.failed s error) = s := rfl

/-- A valid published effect row can carry an out-of-range capture incidence.
The current candidate invariant checks every category named above, but does
not check the `captures` lookup subsequently consumed by `incomingJobs`. -/
def captureGap (caller : NativeValueStructure.Request) : State :=
  {Computed.rowInput caller with
    effects := [⟨2, [], [], [], []⟩]
    captures := fun id => if id = 0 then [⟨99, 0⟩] else []
    work := [.visit ⟨.effect (.row 0), .positive, 1⟩]}

theorem captureGap_valid (caller : NativeValueStructure.Request) :
    RowsValid (captureGap caller) := by
  simp [RowsValid, captureGap, Computed.rowInput, EndpointValid, ValueValid,
    EffectValid, ValueBoundsValid, EffectBoundsValid, KeyValid, WorkValid]

def gapCaller : NativeValueStructure.Request :=
  ⟨.row 0, .row 0, 0, none, 0, none⟩

theorem captureGap_pending_bad :
    .visit ⟨.effect (.row 99), .positive, 1⟩ ∈
      (resultState (step funded (captureGap gapCaller))).pendingBounds := by
  decide

theorem captureGap_effect_count :
    (resultState (step funded (captureGap gapCaller))).effects.length = 2 := by
  decide

theorem captureGap_step_invalid :
    ¬ RowsValid (resultState (step funded (captureGap gapCaller))) := by
  intro valid
  have workValid := valid.2.2.2.2.2.2.2.2.2.1
  have bad := workValid _ captureGap_pending_bad
  have count := captureGap_effect_count
  simp [WorkValid, KeyValid, EndpointValid, EffectValid, count] at bad

def StepPreservesRows : Prop :=
  ∀ (funds : Funding) (s : State), RowsValid s → RowsValid (resultState (step funds s))

def RunPrefixPreservesRows : Prop :=
  ∀ (funds : Funding) (fuel : Nat) (s : State),
    RowsValid s → RowsValid (resultState (runPrefix funds fuel s))

theorem step_preserves_rows_counterexample : ¬ StepPreservesRows := by
  intro preserves
  exact captureGap_step_invalid
    (preserves funded _ (captureGap_valid gapCaller))

theorem runPrefix_preserves_rows_counterexample : ¬ RunPrefixPreservesRows := by
  intro preserves
  exact captureGap_step_invalid
    (show RowsValid (resultState (runPrefix funded 1
      (captureGap gapCaller))) from
      preserves funded 1 _ (captureGap_valid gapCaller))

/-- The existing computed Value row prefix starts from a valid candidate state.
The counterexample above prevents using a universal induction for its prefix. -/
theorem computed_rowInput_valid (caller : NativeValueStructure.Request) :
    RowsValid (Computed.rowInput caller) := by
  simp [RowsValid, Computed.rowInput, EndpointValid, ValueValid, EffectValid,
    ValueBoundsValid, EffectBoundsValid, KeyValid, WorkValid]

end YulangClosure.OriginalExtrusionRowValidityR283
