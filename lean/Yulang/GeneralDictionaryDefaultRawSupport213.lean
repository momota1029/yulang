import Yulang.GeneralDictionaryDefaultJournalFrame212

/-! Reservations are allocation bookkeeping, not semantic observations. Removing
them from the assignment support does not change Models. All base type/row
sources and actual ordinary constraints remain. -/
namespace Yulang.GeneralDictionaryDefaultRawSupport213
open GeneralNominalCenteredFrame179 (Agree)
variable {first last : GeneralNominalCommonBridge.Assignment}

 def sources (state : GeneralNominalState.State) : List Nat :=
  List.ofFn state.base.source ++ List.ofFn state.base.rowSource ++
    state.ordinary.flatMap GeneralNominalState.atomSources

 theorem models_iff (state : GeneralNominalState.State) (same : Agree (sources state) first last) :
    GeneralNominalState.Models state first ↔ GeneralNominalState.Models state last := by
  let reduced : GeneralNominalState.State := {state with reserved := []}
  have agree : Agree (GeneralNominalState.sources reduced) first last := by
    simpa only [GeneralNominalState.sources,reduced,List.append_nil,sources] using same
  exact ⟨GeneralNominalCenteredModelExtension.source_models_same reduced agree,
    GeneralNominalCenteredModelExtension.source_models_same reduced (fun name member => (agree name member).symm)⟩

 theorem subset (state : GeneralNominalState.State) : sources state ⊆ GeneralNominalState.sources state := by
  intro name member
  simp only [sources,List.mem_append] at member
  simp only [GeneralNominalState.sources,List.mem_append]
  rcases member with (left | right) | ordinary
  · exact Or.inl (Or.inl (Or.inl left))
  · exact Or.inl (Or.inl (Or.inr right))
  · exact Or.inr ordinary

 theorem reservations_irrelevant (state : GeneralNominalState.State) (reserved : List Nat) :
    sources {state with reserved := reserved} = sources state := rfl

 theorem models_reservations (state : GeneralNominalState.State) (reserved : List Nat) (model) :
    GeneralNominalState.Models {state with reserved := reserved} model ↔ GeneralNominalState.Models state model := Iff.rfl
end Yulang.GeneralDictionaryDefaultRawSupport213
