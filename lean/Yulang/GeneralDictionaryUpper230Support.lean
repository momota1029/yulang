import Yulang.GeneralDictionaryUpper230Step
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Support
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryOptionalStage229
open GeneralDictionaryUpper230Base GeneralDictionaryUpper230Snapshot GeneralDictionaryUpper230Step

abbrev pool : List Nat := [0,1,2,3,4,lo,hi]

theorem old_support : GeneralNominalState.sources stage.core.erased.current.context.state ⊆ pool := by
  have prior : GeneralNominalState.sources packet.privateContext.state ⊆ pool := by
    apply GeneralNominalAllocationSupport.private_sources packet (List.mem_singleton_self declaration)
    · intro identity member
      have bound := source_bound identity member
      simp only [pool,List.mem_cons,List.not_mem_nil,or_false]
      omega
    · intro identity member
      change identity ∈ [lo,hi,lo,hi] at member
      simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl | rfl | rfl | rfl <;> simp
  exact prior

theorem source_support (slot : Fin 6) : source slot ∈ pool := by
  by_cases old : slot.val < 5
  · simp only [GeneralDictionaryUpper230Base.source,old,ite_true,pool,List.mem_cons,List.not_mem_nil,or_false]
    omega
  · simp [GeneralDictionaryUpper230Base.source,old,pool]

theorem support : GeneralNominalState.sources extendedSnapshot ⊆ pool := by
  intro identity member
  simp only [GeneralNominalState.sources,List.mem_append] at member
  rcases member with ((type | row) | reserved) | ordinary
  · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp type
    exact source_support slot
  · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp row
    exact source_support slot
  · apply old_support
    exact List.mem_append_left _ (List.mem_append_right _ reserved)
  · apply old_support
    exact List.mem_append_right _ ordinary

theorem known_zero : GeneralNominalState.Known extendedSnapshot 0 :=
  ⟨0,rfl,Or.inr ⟨pointDesc,rfl⟩⟩
theorem known_one : GeneralNominalState.Known extendedSnapshot 1 :=
  ⟨1,rfl,Or.inr ⟨pointDesc,rfl⟩⟩
theorem known_two : GeneralNominalState.Known extendedSnapshot 2 :=
  ⟨2,rfl,Or.inl (by decide +kernel)⟩

theorem unknown_cases (member : identity ∈ GeneralNominalState.sources extendedSnapshot)
    (unknown : ¬ GeneralNominalState.Known extendedSnapshot identity) :
    identity = 3 ∨ identity = 4 ∨ identity = lo := by
  have within := support member
  simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at within
  rcases within with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (unknown known_zero)
  · exact False.elim (unknown known_one)
  · exact False.elim (unknown known_two)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact False.elim (unknown GeneralDictionaryUpper230Step.known)

end Yulang.GeneralDictionaryUpper230Support
