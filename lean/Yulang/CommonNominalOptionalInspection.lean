import Yulang.CommonNominalDefaultBounds

/-!
# Constructor inspection for the guarded optional upper form

The upper form is exactly `exactEmpty | required label payload`; it is not
an arbitrary target union. Known source heads reduce to shared-child
comparisons. Different-label record tails and default sources can be followed
at the same constructor depth when their existing width bound holds.

The local width premises are explicit. A generated-clause solver must recover
them from the original width edges; they are not claimed to be automatic for
an arbitrary assignment. No free parameter, regular child or arrow row is
restricted. These rules by themselves do not prove worklist closure.
-/

namespace Yulang.CommonNominalOptionalInspection

open CommonNominalCarrier (Ty Row Subtype)
open CommonNominalOptionalBound (guardedOptional)
open CommonNominalRecordTailProfiles (initialOptional)

theorem not_below_of_no_initial (label : Nat) (source payload : Ty)
    (absent : initialOptional [] label source = false) :
    ¬ Subtype source (guardedOptional label payload) := by
  intro below
  have initial := (CommonNominalOptionalBound.guarded_optional_iff label source payload).mp below |>.1
  simp [absent] at initial

theorem bottom_below (label : Nat) (payload : Ty) :
    Subtype .bottom (guardedOptional label payload) :=
  CommonNominalTypeFlow.bottom_below _

theorem top_not_below (label : Nat) (payload : Ty) :
    ¬ Subtype .top (guardedOptional label payload) :=
  not_below_of_no_initial label .top payload rfl

theorem width_not_below (label : Nat) (payload : Ty) :
    ¬ Subtype CommonNominalCarrier.emptyRecord (guardedOptional label payload) :=
  not_below_of_no_initial label CommonNominalCarrier.emptyRecord payload rfl

theorem exactEmpty_below (label : Nat) (payload : Ty) :
    Subtype CommonNominalCarrier.exactEmpty (guardedOptional label payload) :=
  (CommonNominalOptionalBound.guarded_optional_iff label CommonNominalCarrier.exactEmpty payload).mpr
    ⟨rfl, CommonNominalDefaultRequired.optionalPayload_exactEmpty label payload⟩

theorem base_not_below (scalar : Inference.Base) (label : Nat) (payload : Ty) :
    ¬ Subtype (.base scalar) (guardedOptional label payload) :=
  not_below_of_no_initial label (.base scalar) payload rfl

theorem pair_not_below (first last : Ty) (label : Nat) (payload : Ty) :
    ¬ Subtype (CommonNominalCarrier.pair first last) (guardedOptional label payload) :=
  not_below_of_no_initial label (CommonNominalCarrier.pair first last) payload rfl

theorem variant_not_below (tag : Nat) (child : Ty) (label : Nat) (payload : Ty) :
    ¬ Subtype (CommonNominalCarrier.variant tag child) (guardedOptional label payload) :=
  not_below_of_no_initial label (CommonNominalCarrier.variant tag child) payload rfl

theorem arrow_not_below (input : Ty) (inputRow : Row) (output : Ty) (outputRow : Row)
    (label : Nat) (payload : Ty) :
    ¬ Subtype (CommonNominalCarrier.arrow input inputRow output outputRow) (guardedOptional label payload) :=
  not_below_of_no_initial label (CommonNominalCarrier.arrow input inputRow output outputRow) payload rfl

theorem source_union_iff (first last : Ty) (label : Nat) (payload : Ty) :
    Subtype (.union first last) (guardedOptional label payload) ↔
      Subtype first (guardedOptional label payload) ∧
        Subtype last (guardedOptional label payload) :=
  CommonNominalCarrier.common_union_is_join first last _

/-- A matching record head consumes exactly the selected payload comparison;
the tail is arbitrary and needs no width premise in this rule. -/
theorem record_same_iff (label : Nat) (head tail payload : Ty) :
    Subtype (CommonNominalCarrier.record label head tail) (guardedOptional label payload) ↔ Subtype head payload := by
  rw [CommonNominalOptionalBound.guarded_optional_iff]
  have initial : initialOptional [] label (CommonNominalCarrier.record label head tail) = true := by
    simp [CommonNominalCarrier.record, initialOptional]
  simp only [initial, true_and]
  exact CommonNominalDefaultRequired.optionalPayload_record_same label head tail payload

private theorem width_optional_trivial (source : Ty) (width : Subtype source CommonNominalCarrier.emptyRecord)
    (depth rank : Nat) (env : CommonNominalFinite.Environment Row) (label : Nat) :
    CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy depth source)
      (.optional label .trivial) := by
  apply (CommonNominalFinite.producerLe_iff_probe _ _).mp (width depth) rank env (.optional label .trivial)
  cases rank <;> rfl

private theorem guarded_compare_congr (label : Nat) (first last payload : Ty)
    (same : ∀ depth rank env obs,
      CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy depth first) (.optional label obs) ↔
      CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy depth last) (.optional label obs)) :
    Subtype first (guardedOptional label payload) ↔ Subtype last (guardedOptional label payload) := by
  constructor
  · intro below depth
    apply (CommonNominalOptionalBound.finite_optional_iff _ _ label).mpr
    intro rank env obs accepted
    exact (same depth rank env obs).mp
      ((CommonNominalOptionalBound.finite_optional_iff _ _ label).mp (below depth) rank env obs accepted)
  · intro below depth
    apply (CommonNominalOptionalBound.finite_optional_iff _ _ label).mpr
    intro rank env obs accepted
    exact (same depth rank env obs).mpr
      ((CommonNominalOptionalBound.finite_optional_iff _ _ label).mp (below depth) rank env obs accepted)

theorem record_other_iff (current label : Nat) (head tail payload : Ty)
    (different : label ≠ current) (width : Subtype tail CommonNominalCarrier.emptyRecord) :
    Subtype (CommonNominalCarrier.record current head tail) (guardedOptional label payload) ↔
      Subtype tail (guardedOptional label payload) := by
  apply guarded_compare_congr
  intro depth rank env obs
  change CommonNominalFinite.ProbeAt Common.rowLe rank env
    (.record current _ (CommonNominalCarrier.observeTy depth tail)) (.optional label obs) ↔ _
  rw [CommonNominalFinite.probeAt_record_optional]
  simp only [different, ↓reduceIte]
  constructor
  · rintro (accepted | rfl)
    · exact accepted
    · exact width_optional_trivial tail width depth rank env label
  · exact Or.inl

theorem required_same_iff (label : Nat) (head payload : Ty) :
    Subtype (CommonNominalCarrier.required label head) (guardedOptional label payload) ↔ Subtype head payload :=
  record_same_iff label head CommonNominalCarrier.emptyRecord payload

theorem required_other_not_below (current label : Nat) (head payload : Ty)
    (different : label ≠ current) :
    ¬ Subtype (CommonNominalCarrier.required current head) (guardedOptional label payload) := by
  intro below
  exact width_not_below label payload
    ((record_other_iff current label head CommonNominalCarrier.emptyRecord payload different
      (CommonNominalCarrier.subtype_refl _)).mp below)

theorem guarded_same_iff (label : Nat) (head payload : Ty) :
    Subtype (guardedOptional label head) (guardedOptional label payload) ↔ Subtype head payload := by
  constructor
  · intro below
    have parts := (source_union_iff CommonNominalCarrier.exactEmpty (CommonNominalCarrier.required label head) label payload).mp below
    exact (required_same_iff label head payload).mp parts.2
  · intro below
    exact (source_union_iff CommonNominalCarrier.exactEmpty (CommonNominalCarrier.required label head) label payload).mpr
      ⟨exactEmpty_below label payload, (required_same_iff label head payload).mpr below⟩

theorem guarded_other_not_below (current label : Nat) (head payload : Ty)
    (different : label ≠ current) :
    ¬ Subtype (guardedOptional current head) (guardedOptional label payload) := by
  intro below
  exact required_other_not_below current label head payload different
    ((source_union_iff CommonNominalCarrier.exactEmpty (CommonNominalCarrier.required current head) label payload).mp below).2

theorem default_other_iff (current label : Nat) (source fallback payload : Ty)
    (different : label ≠ current) (width : Subtype source CommonNominalCarrier.emptyRecord) :
    Subtype (CommonNominalCarrier.recordDefault current source fallback) (guardedOptional label payload) ↔
      Subtype source (guardedOptional label payload) := by
  apply guarded_compare_congr
  intro depth rank env obs
  have finish :
      (CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy depth source)
        (.optional label obs) ∨ obs = .trivial) ↔
      CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy depth source)
        (.optional label obs) := by
    constructor
    · rintro (accepted | rfl)
      · exact accepted
      · exact width_optional_trivial source width depth rank env label
    · exact Or.inl
  cases depth with
  | zero =>
      change CommonNominalFinite.ProbeAt Common.rowLe rank env
        (.record current .bottom (CommonNominalCarrier.observeTy 0 source)) (.optional label obs) ↔ _
      simpa only [CommonNominalFinite.probeAt_record_optional, different, ↓reduceIte] using finish
  | succ depth =>
      change CommonNominalFinite.ProbeAt Common.rowLe rank env
        (.recordDefault current (CommonNominalCarrier.observeTy (depth + 1) source) (CommonNominalCarrier.observeTy depth fallback))
        (.optional label obs) ↔ _
      simpa only [CommonNominalFinite.probeAt_default_optional, different, ↓reduceIte] using finish

theorem default_same_iff (label : Nat) (source fallback payload : Ty)
    (width : Subtype source CommonNominalCarrier.emptyRecord) :
    Subtype (CommonNominalCarrier.recordDefault label source fallback) (guardedOptional label payload) ↔
      Subtype (CommonNominalCarrier.recordDefault label source fallback) (CommonNominalCarrier.required label payload) := by
  have same (depth rank : Nat) (env : CommonNominalFinite.Environment Row) (obs : CommonNominalCarrier.Observation) :
      CommonNominalFinite.ProbeAt Common.rowLe rank env
          (CommonNominalCarrier.observeTy depth (CommonNominalCarrier.recordDefault label source fallback)) (.optional label obs) ↔
      CommonNominalFinite.ProbeAt Common.rowLe rank env
          (CommonNominalCarrier.observeTy depth (CommonNominalCarrier.recordDefault label source fallback)) (.field label obs) := by
    cases depth with
    | zero =>
        change CommonNominalFinite.ProbeAt Common.rowLe rank env
          (.record label .bottom (CommonNominalCarrier.observeTy 0 source)) (.optional label obs) ↔
          CommonNominalFinite.ProbeAt Common.rowLe rank env
            (.record label .bottom (CommonNominalCarrier.observeTy 0 source)) (.field label obs)
        simp only [CommonNominalFinite.probeAt_record_optional, CommonNominalFinite.probeAt_record_field, ↓reduceIte]
    | succ depth =>
        change CommonNominalFinite.ProbeAt Common.rowLe rank env
          (.recordDefault label (CommonNominalCarrier.observeTy (depth + 1) source) (CommonNominalCarrier.observeTy depth fallback))
          (.optional label obs) ↔ CommonNominalFinite.ProbeAt Common.rowLe rank env
          (.recordDefault label (CommonNominalCarrier.observeTy (depth + 1) source) (CommonNominalCarrier.observeTy depth fallback))
          (.field label obs)
        rw [CommonNominalFinite.probeAt_default_optional, CommonNominalFinite.probeAt_default_field]
        simp only [↓reduceIte]
        constructor
        · rintro (accepted | rfl)
          · exact accepted
          · exact ⟨width_optional_trivial source width (depth + 1) rank env label,
              Or.inr (CommonNominalFinite.probeAt_trivial rank _)⟩
        · exact Or.inl
  constructor
  · intro below depth
    apply (CommonNominalRecordTargetProfiles.finite_required_iff _ _ label).mpr
    intro rank env obs accepted
    exact (same depth rank env obs).mp
      ((CommonNominalOptionalBound.finite_optional_iff _ _ label).mp (below depth) rank env obs accepted)
  · intro below depth
    apply (CommonNominalOptionalBound.finite_optional_iff _ _ label).mpr
    intro rank env obs accepted
    exact (same depth rank env obs).mpr
      ((CommonNominalRecordTargetProfiles.finite_required_iff _ _ label).mp (below depth) rank env obs accepted)

theorem default_same_branches_exact (label : Nat) (source fallback payload : Ty)
    (width : Subtype source CommonNominalCarrier.emptyRecord) :
    Subtype (CommonNominalCarrier.recordDefault label source fallback) (guardedOptional label payload) ↔
      (Subtype .top payload ∧ Subtype source CommonNominalCarrier.emptyRecord) ∨
      (Subtype source (guardedOptional label payload) ∧
        Subtype source (CommonNominalCarrier.required label .top)) ∨
      (Subtype source (guardedOptional label payload) ∧ Subtype fallback payload) := by
  rw [default_same_iff label source fallback payload width,
    CommonNominalDefaultBounds.default_required_branches_exact]

theorem float_not_below (label : Nat) (payload : Ty) :
    ¬ Subtype .float (guardedOptional label payload) :=
  not_below_of_no_initial label .float payload rfl

theorem nominal_not_below (name : Nat) (arguments : List CommonNominalCarrier.Argument)
    (label : Nat) (payload : Ty) :
    ¬ Subtype (CommonNominalCarrier.nominal name arguments) (guardedOptional label payload) :=
  not_below_of_no_initial label (CommonNominalCarrier.nominal name arguments) payload rfl

end Yulang.CommonNominalOptionalInspection
