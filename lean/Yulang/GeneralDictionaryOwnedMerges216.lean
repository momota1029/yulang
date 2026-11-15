import Yulang.GeneralDictionaryPointExtrema216

/-! Installed aggregate slots are reused, never overwritten, when their old and
current extrema are equivalent. This complements the disjoint-slot constructor.
Neither stability nor point captures is asserted for every reachable packet. -/
namespace Yulang.GeneralDictionaryOwnedMerges216
open GeneralDeclarations GeneralNominalAllocation CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryMergeSlots216 GeneralDictionaryPointExtrema216

 theorem capture_slots (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (name : Nat)
    (_nonsingle : ∀ pair, occurrences bindings name ≠ [pair]) :
    (capture state registry invocation declaration.id bindings).inputs name =
      (slot state registry invocation declaration 0 name,slot state registry invocation declaration 1 name) := by
  simp only [capture]
  rfl

 theorem transfer (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (first last : Bindings) (model : Assignment)
    (recorded : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges state registry invocation declaration first))
    (stable : ∀ name ∈ declaration.inputNames, (∀ pair, occurrences last name ≠ [pair]) →
      (∀ pair, occurrences first name ≠ [pair]) ∧
      Equivalent ((lower (occurrences first name)).eval CommonNominalFullCarrier.model model)
        ((lower (occurrences last name)).eval CommonNominalFullCarrier.model model) ∧
      Equivalent ((upper (occurrences first name)).eval CommonNominalFullCarrier.model model)
        ((upper (occurrences last name)).eval CommonNominalFullCarrier.model model)) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges state registry invocation declaration last) := by
  apply (GeneralNominalMergeResidual178.merges_iff_extrema ..).mpr
  intro name declared bounds observed nonsingle
  have current : ∀ pair, occurrences last name ≠ [pair] :=
    fun pair equal => nonsingle pair (observed.symm.trans equal)
  obtain ⟨oldSingle,lowerSame,upperSame⟩ := stable name declared current
  have old := (GeneralNominalMergeResidual178.merges_iff_extrema ..).mp recorded name declared
    (occurrences first name) rfl oldSingle
  rw [capture_slots state registry invocation declaration first name oldSingle] at old
  rw [capture_slots state registry invocation declaration last name current,← observed]
  exact ⟨⟨subtype_trans old.1.1 lowerSame.1,subtype_trans lowerSame.2 old.1.2⟩,
    ⟨subtype_trans old.2.1 upperSame.1,subtype_trans upperSame.2 old.2.2⟩⟩

 theorem point_transfer (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (first last : Bindings) (model : Assignment)
    (recorded : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges state registry invocation declaration first))
    (point : ∀ name ∈ declaration.inputNames, (∀ pair, occurrences last name ≠ [pair]) →
      (∀ pair, occurrences first name ≠ [pair]) ∧ occurrences first name ≠ [] ∧ occurrences last name ≠ [] ∧
      ∃ value, Points model (occurrences first name) value ∧ Points model (occurrences last name) value) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges state registry invocation declaration last) := by
  apply transfer state registry invocation declaration first last model recorded
  intro name declared nonsingle
  obtain ⟨oldSingle,oldNonempty,newNonempty,value,oldPoint,newPoint⟩ := point name declared nonsingle
  exact ⟨oldSingle,extrema_same model _ _ value oldNonempty newNonempty oldPoint newPoint⟩

end Yulang.GeneralDictionaryOwnedMerges216
