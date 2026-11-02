import YulangClosure.OriginalExtrusionRowValidityR283

/-!
The capture incidence consumed by `incomingJobs` names an Effect row.  Its
canonical representative must also be a published Effect row.  This is a
candidate storage invariant in the existing operation-local model, not a
source-to-native correspondence theorem.
-/
namespace YulangClosure.OriginalExtrusionCaptureValidityR284

open OriginalExtrusionWork
open OriginalExtrusionRowValidityR283

def CaptureSourceValid (s : State) (source : Nat) : Prop :=
  source < s.effects.length ∧ s.qe source < s.effects.length

def CapturesValid (s : State) : Prop :=
  ∀ id, ∀ incidence ∈ s.captures id, CaptureSourceValid s incidence.source

def CaptureComplete (s : State) : Prop := RowsValid s ∧ CapturesValid s

theorem capture_complete_rows (s : State) (h : CaptureComplete s) : RowsValid s := h.1

theorem capture_complete_sources (s : State) (h : CaptureComplete s)
    (id : Nat) (incidence : Capture)
    (hm : incidence ∈ s.captures id) :
    CaptureSourceValid s incidence.source := h.2 id incidence hm

theorem capture_source_valid_of_same_effects_qe (s t : State) (source : Nat)
    (he : t.effects = s.effects) (hq : t.qe source = s.qe source)
    (h : CaptureSourceValid s source) : CaptureSourceValid t source := by
  simp only [CaptureSourceValid, he, hq]
  exact h

theorem capture_source_valid_canonical_change (s t : State) (source : Nat)
    (he : t.effects = s.effects)
    (hs : source < s.effects.length)
    (hq : t.qe source < s.effects.length) : CaptureSourceValid t source := by
  simp only [CaptureSourceValid, he]
  exact ⟨hs, hq⟩

theorem capture_source_valid_allocate (s : State) (key : CopyKey) (source : Nat)
    (h : CaptureSourceValid s source) :
    CaptureSourceValid (s.allocate key) source := by
  cases key with
  | mk endpoint polarity target => cases endpoint with
    | value endpoint => simpa [CaptureSourceValid, State.allocate] using h
    | effect endpoint =>
      rcases h with ⟨hs, hq⟩
      simp only [CaptureSourceValid, State.allocate, List.length_append,
        List.length_singleton, Nat.add_one]
      constructor
      · omega
      · have hne : source ≠ s.effects.length := by omega
        simp [hne]
        omega

theorem captures_valid_allocate (s : State) (key : CopyKey)
    (h : CapturesValid s) : CapturesValid (s.allocate key) := by
  intro id incidence hm
  apply capture_source_valid_allocate s key incidence.source
  apply h id incidence
  cases key with
  | mk endpoint polarity target => cases endpoint with
    | value endpoint => simpa [State.allocate] using hm
    | effect endpoint => simpa [State.allocate] using hm

theorem captures_valid_pushed (s : State) (pending : Bool) (items : List Work)
    (h : CapturesValid s) : CapturesValid (pushed pending items s) := by
  cases pending <;> simpa [CapturesValid, pushed, CaptureSourceValid] using h

theorem incoming_child_valid (s : State)
    (key : CopyKey) (incidence : Capture)
    (h : CaptureSourceValid s incidence.source) :
    KeyValid s ⟨s.canonical (.effect (.row incidence.source)), .positive, key.target⟩ := by
  simpa [KeyValid, EndpointValid, EffectValid, State.canonical,
    NativeMergeExpansion.renameEndpoint] using h.2

theorem incoming_visit_queued (s : State) (id tail : Nat)
    (incidence : Capture) (target : Nat)
    (hm : incidence ∈ s.captures id) :
    .visit ⟨s.canonical (.effect (.row incidence.source)), .positive, target⟩ ∈
      incomingJobs s ⟨.effect (.row id), .positive, target⟩ (.effect (.row tail)) := by
  simp only [incomingJobs, List.mem_flatMap, List.mem_reverse]
  exact ⟨incidence, hm, by simp⟩

theorem incoming_visit_queued_valid (s : State) (id : Nat)
    (incidence : Capture) (target : Nat)
    (h : CapturesValid s) (hm : incidence ∈ s.captures id) :
    KeyValid s ⟨s.canonical (.effect (.row incidence.source)), .positive, target⟩ := by
  exact incoming_child_valid s ⟨.effect (.row id), .positive, target⟩ incidence
    (h id incidence hm)

theorem capture_gap_excluded (caller : NativeValueStructure.Request) :
    ¬ CaptureComplete (captureGap caller) := by
  intro h
  have hs := h.2 0 (⟨99, 0⟩ : Capture)
    (by simp [captureGap])
  simp [CaptureSourceValid, captureGap] at hs

theorem computed_rowInput_capture_complete (caller : NativeValueStructure.Request) :
    CaptureComplete (Computed.rowInput caller) := by
  constructor
  · exact computed_rowInput_valid caller
  · simp [CapturesValid, Computed.rowInput]

/-- An effect-view tail is a separate storage reference.  The existing model
permits a published view whose tail is not a published row. -/
def viewTailGap : State :=
  {Computed.rowInput gapCaller with
    effects := [⟨0, [], [], [], []⟩]
    views := fun view => if view = 7 then some (some 99) else none
    work := [.visit ⟨.effect (.allowance 7), .positive, 0⟩]}

theorem view_tail_gap_capture_complete : CaptureComplete viewTailGap := by
  constructor
  · simp [RowsValid, viewTailGap, Computed.rowInput, EndpointValid, ValueValid,
      EffectValid, ValueBoundsValid, EffectBoundsValid, KeyValid, WorkValid]
  · simp [CapturesValid, viewTailGap, Computed.rowInput]

theorem view_tail_gap_pending_bad :
    .visit ⟨.effect (.row 99), .positive, 0⟩ ∈
      (resultState (step funded viewTailGap)).work := by
  decide

theorem view_tail_gap_next :
    step funded viewTailGap = .next (resultState (step funded viewTailGap)) := by
  rfl

theorem view_tail_gap_effect_count :
    (resultState (step funded viewTailGap)).effects.length = 1 := by
  decide

theorem view_tail_gap_step_invalid :
    ¬ CaptureComplete (resultState (step funded viewTailGap)) := by
  intro h
  have workValid := h.1.2.2.2.2.2.2.2.2.1
  have bad := workValid _ view_tail_gap_pending_bad
  have count := view_tail_gap_effect_count
  simp [WorkValid, KeyValid, EndpointValid, EffectValid, count] at bad

def StepPreservesCaptureComplete : Prop :=
  ∀ (funds : Funding) (s : State), CaptureComplete s →
    CaptureComplete (resultState (step funds s))

theorem step_preserves_capture_complete_counterexample :
    ¬ StepPreservesCaptureComplete := by
  intro preserves
  exact view_tail_gap_step_invalid
    (preserves funded viewTailGap view_tail_gap_capture_complete)

end YulangClosure.OriginalExtrusionCaptureValidityR284
