import Yulang.GeneralDictionaryHistoricalNominalRefreshExample

/-! Full-journal and raw K2 exclusion for the actual carrier-changing fixture.
These are independent selection guards, not a claim of completed selection. -/
namespace Yulang.GeneralDictionaryHistoricalRefreshSelection
open GeneralDictionaryMixedCatalogExample GeneralDictionaryMixedCarrierRefresh
open GeneralNominalExamples (displayRoot model)
private def height (source : Nat) : Nat := if source = 0 then 1 else 0
private theorem model_height (source : Nat) :
    (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

theorem feedback_acyclic (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle refreshed.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model refreshed_inhabited
    height model_height (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem raw_acyclic (slot : Fin snapshot.base.slots) : ¬ GeneralNominalCycleK2.Cycle snapshot slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge snapshot first last →
      height (snapshot.base.source last) < height (snapshot.base.source first) := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model refreshed_inhabited.1
      exact GeneralNominalOutputGrowthModels.observation_decreases model height model_height _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path snapshot first last →
      height (snapshot.base.source last) ≤ height (snapshot.base.source first) := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

theorem no_raw_recurs (slot : Fin snapshot.base.slots) : ¬ GeneralNominalCycleK2.RecursAt snapshot slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle

theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 refreshed.current displayRoot := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact no_raw_recurs slot cycle
  · exact feedback_acyclic _ cycle

theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry refreshed.current displayRoot := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw_recurs visited.1 cycle
  · exact feedback_acyclic _ cycle
end Yulang.GeneralDictionaryHistoricalRefreshSelection
