import Yulang.GeneralDictionaryVersionedAcyclic232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedRawAcyclic232
open GeneralDictionaryVersionedInstalled232
open GeneralDictionaryVersionedNames231
open GeneralDictionaryOptionalCycles229
open GeneralDictionaryUpper230Base (source viewShapes)
open GeneralNominalRecursiveInspection CommonNominalFullCarrier

noncomputable abbrev current := installed.core.erased.current.context

theorem source_form (slot : Fin 6) :
    (extended (source slot)).1 = (GeneralDictionaryOptionalStageSafety229.sourceForm (source slot)).value := by
  have within : ∀ slot : Fin 6, source slot ∈ GeneralDictionaryVersionedSupport231.pool := by decide +kernel
  rw [old_value _ (within slot)]
  exact GeneralDictionaryOptionalStageSafety229.model_form _

theorem raw_model : GeneralNominalState.Models current.state extended :=
  GeneralDictionaryVersionedAcyclic232.installed_model.1.1

theorem raw_edge_decreases {a b : Fin 6} (edge : GeneralNominalMixedRecurrence.Edge current.state a b) :
    (GeneralDictionaryOptionalStageSafety229.sourceForm (source b)).rank <
      (GeneralDictionaryOptionalStageSafety229.sourceForm (source a)).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 ∨ a = 5 then .structural 0 Fin.elim0 else .deferred .unresolved :
      GeneralNormalizedObservation.Head viewShapes 6) = .structural kind children at recorded
    split at recorded
    · cases recorded; exact Fin.elim0 index
    · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound current.state a b nominal extended raw_model
    have observation := embed_observation extended _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      change Equivalent (extended (source a)).1 _ at equal
      rw [source_form] at equal
      obtain ⟨child,smaller,meaning⟩ := nominal_child
        (GeneralDictionaryOptionalStageSafety229.sourceForm (source a)) equal found
      change Equivalent _ (extended (source b)).1 at same
      rw [source_form] at same
      have rankEq := equivalent_rank child
        (GeneralDictionaryOptionalStageSafety229.sourceForm (source b))
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem no_raw_recurs (slot : Fin 6) : ¬ GeneralNominalCycleK2.RecursAt current.state slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path current.state a b →
      (GeneralDictionaryOptionalStageSafety229.sourceForm (source b)).rank ≤
      (GeneralDictionaryOptionalStageSafety229.sourceForm (source a)).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have smaller := raw_edge_decreases edge
  have larger := paths _ _ path
  omega

end Yulang.GeneralDictionaryVersionedRawAcyclic232
