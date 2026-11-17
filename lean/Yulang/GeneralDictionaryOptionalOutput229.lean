import Yulang.GeneralDictionaryInspectionHeads215

/-! A representable optional-field output with no exact normalized head.
This is a carrier-level probe, not yet a stable reachable journal example. -/
namespace Yulang.GeneralDictionaryOptionalOutput229
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralDictionaryInspectionHeads215
open GeneralNominalFiniteMeaning

abbrev value : Ty := .union .exactEmpty (record 0 .emptyRecord .exactEmpty)

theorem tagged : Tagged value .records := by
  intro env
  change (_ ∈ env.roles 0 ∧ _ ∈ env.roles 0) ↔ _
  exact and_self_iff

theorem no_field (label : Nat) :
    ¬ CommonNominalFullDemand.ProbeAt Common.rowLe 0 ⟨fun _ => .bottom,fun _ => []⟩
      (observeTy 0 value) (.field label .trivial) := by
  intro held
  exact held.1

theorem not_width : ¬ Equivalent value .emptyRecord := by
  intro equal
  have held := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.2 1) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.optional 0 .records) (by
      constructor
      · exact Or.inl (by simp)
      · change (if (0 : Nat) = 0 ∧ 0 ∉ ([] : List Nat) then True else _)
        simp)
  change (CommonNominalFinite.Observation.records : CommonNominalFinite.Observation Row) = .trivial at held
  cases held

theorem not_exact : ¬ Equivalent value .exactEmpty := by
  intro equal
  have held := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 1) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.optional 0 .impossible) (by exact Or.inl (by simp))
  have impossible := held.2
  change (if (0 : Nat) = 0 ∧ 0 ∉ ([] : List Nat) then False else _) at impossible
  simp at impossible

theorem no_test (test : Test) : ¬ test.Holds value := by
  intro held
  have same := tag_subtype tagged (tagged_test test held) (subtype_refl value)
  cases test with
  | scalar => cases same
  | nominal => cases same
  | structural shape =>
    cases shape with
    | pair | variant => cases same
    | exactEmpty =>
      obtain ⟨values,length,equal⟩ := held
      exact not_exact equal
    | record labels =>
      obtain ⟨values,length,equal⟩ := held
      rw [GeneralNominalRecordInversion.record_shape labels values length] at equal
      cases labels with
      | nil => exact not_width equal
      | cons label labels =>
        have nonempty : label ∈ ((label :: labels).zip values).map Prod.fst := by
          rw [List.map_fst_zip (Nat.le_of_eq length.symm)]
          simp
        have accepted := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0
          ⟨fun _ => .bottom,fun _ => []⟩ (.field label .trivial)
          ((GeneralNominalRecordInversion.field_presence _ label).mpr nonempty)
        exact no_field label accepted

theorem below_width : Subtype value .emptyRecord := by
  apply (common_union_is_join ..).mpr
  refine ⟨exactEmpty_below_width,?_⟩
  intro depth
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;>
    simp_all [observeTy,record,CommonNominalSyntax.Layer.evalAt,
      CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,
      CommonNominalFullDemand.MaskedProbeStep]

theorem width_not_below : ¬ Subtype .emptyRecord value :=
  fun below => not_width ⟨below_width,below⟩

/-- The output is not bottom either: exact-empty already excludes the
impossible observation, which every bottom accepts. -/
theorem not_bottom : ¬ Equivalent value .bottom := by
  intro equal
  have held := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ .impossible (by trivial)
  exact held.1

end Yulang.GeneralDictionaryOptionalOutput229
