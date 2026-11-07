import Yulang.ProducerContextualRegular

/-!
# Passing only remaining field requirements to a record tail

The head of `record label payload rest` discharges its own field demand.
The tail receives only demands for other labels. It is not compared under
the original demand, nor under an invented `label : any` requirement.
The relative field relation below is defined by the same contextual probes,
including all ranks, environments, nested masks and role observations.
-/

namespace Yulang.ProducerContextualRecord

open Inference StructuralBase ProducerContextual

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

/-- Compare just the field requirements left after the named heads have
already been handled. This is not whole-type comparison of the tails. -/
def FieldLe (leRow : Row → Row → Prop) (hidden : List Nat) (source target : Ty Row) : Prop :=
  ∀ rank env label, label ∉ hidden → ∀ observation,
    ProbeAt leRow rank env target (.field label observation) →
      ProbeAt leRow rank env source (.field label observation)

theorem fieldLe_refl (hidden : List Nat) (type : Ty Row) : FieldLe leRow hidden type type :=
  fun _ _ _ _ _ accepted => accepted

theorem fieldLe_trans (hidden : List Nat) {first middle last : Ty Row}
    (left : FieldLe leRow hidden first middle) (right : FieldLe leRow hidden middle last) :
    FieldLe leRow hidden first last :=
  fun rank env label visible observation accepted =>
    left rank env label visible observation (right rank env label visible observation accepted)

theorem fieldLe_hide_more {first last : List Nat}
    (more : ∀ label ∈ first, label ∈ last) {source target : Ty Row}
    (below : FieldLe leRow first source target) : FieldLe leRow last source target :=
  fun rank env label visible observation accepted =>
    below rank env label (fun member => visible (more label member)) observation accepted

theorem probeAt_record_field (rank : Nat) (env : Environment Row)
    (current label : Nat) (payload rest : Ty Row) (observation : Observation Row) :
    ProbeAt leRow rank env (.record current payload rest) (.field label observation) ↔
      if label = current then ProbeAt leRow rank env payload observation
      else ProbeAt leRow rank env rest (.field label observation) := by
  cases rank <;> rfl

/-- Relative comparison of two equal heads splits into their visible payload
and the remaining tail demands. Hiding the head removes its payload demand. -/
theorem fieldLe_record_iff (hidden : List Nat) (label : Nat) (a b rest tail : Ty Row) :
    FieldLe leRow hidden (.record label a rest) (.record label b tail) ↔
      (label ∉ hidden → ProducerLe leRow a b) ∧ FieldLe leRow (label :: hidden) rest tail := by
  constructor
  · intro below
    constructor
    · intro visible
      apply (producerLe_iff_probe _ _).mpr
      intro rank env observation accepted
      have projected := below rank env label visible observation
      simp only [probeAt_record_field, ↓reduceIte] at projected
      exact projected accepted
    · intro rank env current visible observation accepted
      have facts : current ≠ label ∧ current ∉ hidden := by simpa using visible
      have different := facts.1
      have prior := facts.2
      have projected := below rank env current prior observation
      simp only [probeAt_record_field, different, ↓reduceIte] at projected
      exact projected accepted
  · rintro ⟨payload, remaining⟩ rank env current visible observation accepted
    by_cases same : current = label
    · subst current
      have projected := (producerLe_iff_probe _ _).mp (payload visible) rank env observation
      simp only [probeAt_record_field, ↓reduceIte] at accepted ⊢
      exact projected accepted
    · have projected := remaining rank env current (by simp [same, visible]) observation
      simp only [probeAt_record_field, same, ↓reduceIte] at accepted ⊢
      exact projected accepted

/-- The outer record already discharges all record-kind and role-head tests;
the comparison that remains is exactly comparison of its field observations. -/
theorem producerLe_records_iff_fields (first last : Nat) (a b rest tail : Ty Row) :
    ProducerLe leRow (.record first a rest) (.record last b tail) ↔
      FieldLe leRow [] (.record first a rest) (.record last b tail) := by
  constructor
  · intro below rank env label _ observation accepted
    exact (producerLe_iff_probe _ _).mp below rank env (.field label observation) accepted
  · intro fields
    apply (producerLe_iff_probe _ _).mpr
    intro rank env observation accepted
    cases observation with
    | field label payload => exact fields rank env label (by simp) payload accepted
    | _ => cases rank <;> exact accepted

/-- The exact record-head decomposition required by spec 4.3. No row laws,
well-formedness or successful-solver hypothesis is needed for this equality. -/
theorem producerLe_record_iff (label : Nat) (a b rest tail : Ty Row) :
    ProducerLe leRow (.record label a rest) (.record label b tail) ↔
      ProducerLe leRow a b ∧ FieldLe leRow [label] rest tail := by
  rw [producerLe_records_iff_fields, fieldLe_record_iff]
  simp

theorem fieldLe_emptyRecord (hidden : List Nat) (source : Ty Row) :
    FieldLe leRow hidden source .emptyRecord := by
  intro rank env label _ observation accepted
  cases rank <;> exact False.elim accepted

/-- In a singleton required-field target the tail receives no field demand. -/
theorem singleton_requirement_iff (label : Nat) (a b rest : Ty Row) :
    ProducerLe leRow (.record label a rest) (.record label b .emptyRecord) ↔
      ProducerLe leRow a b := by
  rw [producerLe_record_iff]
  exact and_iff_left (fieldLe_emptyRecord [label] rest)

/-- Reintroducing an already hidden head cannot affect any remaining field. -/
theorem hidden_head_iff (hidden : List Nat) (label : Nat) (payload rest target : Ty Row) :
    FieldLe leRow (label :: hidden) (.record label payload rest) target ↔
      FieldLe leRow (label :: hidden) rest target := by
  constructor <;> intro below rank env current visible observation accepted
  · have projected := below rank env current visible observation accepted
    have different : current ≠ label := fun same => visible (List.mem_cons.mpr (Or.inl same))
    simpa only [probeAt_record_field, different, ↓reduceIte] using projected
  · have projected := below rank env current visible observation accepted
    have different : current ≠ label := fun same => visible (List.mem_cons.mpr (Or.inl same))
    simpa only [probeAt_record_field, different, ↓reduceIte] using projected

theorem shadowed_head_equivalent (label : Nat) (payload hidden rest : Ty Row) :
    ProducerEq leRow (.record label payload (.record label hidden rest)) (.record label payload rest) := by
  constructor
  · apply (producerLe_record_iff _ _ _ _ _).mpr
    exact ⟨producerLe_refl payload, (hidden_head_iff [] label hidden rest rest).mpr (fieldLe_refl _ _)⟩
  · apply (producerLe_record_iff _ _ _ _ _).mpr
    refine ⟨producerLe_refl payload, ?_⟩
    intro rank env current visible observation accepted
    have different : current ≠ label := fun same => visible (List.mem_cons.mpr (Or.inl same))
    simpa only [probeAt_record_field, different, ↓reduceIte] using accepted

namespace Regular

open RegularValueTypes

universe v
variable {State : Type v}

def FieldLe (graph : Graph Row State) (leRow : Row → Row → Prop) (hidden : List Nat)
    (source target : Layer Row State) : Prop :=
  ∀ depth, ProducerContextualRecord.FieldLe leRow hidden
    (source.eval (observe graph depth)) (target.eval (observe graph depth))

/-- Every graph and every constructor depth are covered; the tail is still
a finite layer here, and is compared at exactly the original depth. -/
theorem record_reference_iff (graph : Graph Row State) (label : Nat)
    (a b : State) (rest tail : Layer Row State) :
    ProducerContextualRegular.ProducerLe graph leRow (.record label a rest) (.record label b tail) ↔
      ProducerContextualRegular.ReferenceLe graph leRow a b ∧ FieldLe graph leRow [label] rest tail := by
  constructor
  · intro below
    have split := fun depth => (producerLe_record_iff label _ _ _ _).mp (below depth)
    exact ⟨fun depth => (split depth).1, fun depth => (split depth).2⟩
  · rintro ⟨payload, remaining⟩ depth
    exact (producerLe_record_iff label _ _ _ _).mpr ⟨payload depth, remaining depth⟩

theorem record_iff (label : Nat) (a b rest tail : RegularInferenceModel.Ty Row) :
    ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Row) leRow
      (.record label (.node a) rest) (.record label (.node b) tail) ↔
      ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Row) leRow a b ∧
        FieldLe (RegularInferenceModel.graph Row) leRow [label] rest tail := by
  constructor
  · intro below
    have split := (record_reference_iff (RegularInferenceModel.graph Row) label _ _ _ _).mp below
    exact ⟨fun depth => split.1 (depth + 1), split.2⟩
  · rintro ⟨payload, remaining⟩
    apply (record_reference_iff (RegularInferenceModel.graph Row) label _ _ _ _).mpr
    exact ⟨fun depth => ProducerContextualRegular.quote_observe_le payload depth, remaining⟩

theorem singleton_requirement_iff (label : Nat) (a b rest : RegularInferenceModel.Ty Row) :
    ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Row) leRow
      (.record label (.node a) rest) (.record label (.node b) .emptyRecord) ↔
      ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Row) leRow a b := by
  rw [record_iff]
  exact and_iff_left (fun depth => fieldLe_emptyRecord [label] _)

theorem shadowed_head_equivalent (graph : Graph Row State) (label : Nat)
    (payload hidden : State) (rest : Layer Row State) :
    ProducerContextualRegular.ProducerEq graph leRow
      (.record label payload (.record label hidden rest)) (.record label payload rest) := by
  exact ⟨fun depth => (ProducerContextualRecord.shadowed_head_equivalent label _ _ _).1,
    fun depth => (ProducerContextualRecord.shadowed_head_equivalent label _ _ _).2⟩

end Regular

end Yulang.ProducerContextualRecord
