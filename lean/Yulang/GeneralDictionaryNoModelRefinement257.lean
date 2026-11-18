import Yulang.GeneralDictionaryFiniteView257
namespace Yulang.GeneralDictionaryNoModelRefinement257
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryFiveSlot257 (view)
open GeneralDictionaryCompactFields257 (pair)
open GeneralDictionaryOrdinaryFinite257 (candidates le)
open GeneralNominalRebaseRawView243 (View Descriptor FitsAll Parameter)
open CommonNominalFullCarrier

theorem initial_cross (assignment : Assignment) (valid : (view 0).Models assignment) :
 Subtype (assignment 2).1 (assignment 4).1 := by
 have descriptor := valid.2.2.2 (3 : Fin 5) pair rfl
 obtain ⟨values,fits,_⟩ := descriptor
 cases fits with
 | cons first rest =>
   rename_i value values
   cases value with
   | inl value => exact subtype_trans first.1 first.2
   | inr value => exact False.elim first

theorem initial_facts (assignment : Assignment) (valid : (view 0).Models assignment) :
 All model assignment candidates := by
 intro atom member
 simp only [candidates,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl
 · exact initial_cross assignment valid
 all_goals exact subtype_refl _

theorem one_iff_zero (assignment : Assignment) :
 (view 1).Models assignment ↔ (view 0).Models assignment := by
 constructor
 · intro valid
   refine ⟨?_,valid.2⟩
   change All model assignment (GeneralDictionaryCompactFields257.baseFacts ++ [])
   have ordinary := valid.1
   change All model assignment (GeneralDictionaryCompactFields257.baseFacts ++ candidates) at ordinary
   exact (all_append ..).mpr ⟨(all_append ..).mp ordinary |>.1,by intro atom member; cases member⟩
 · intro valid
   refine ⟨?_,valid.2⟩
   change All model assignment (GeneralDictionaryCompactFields257.baseFacts ++ candidates)
   exact (all_append ..).mpr ⟨(all_append ..).mp valid.1 |>.1,initial_facts assignment valid⟩

theorem all_iff_zero (n : Nat) (assignment : Assignment) :
 (view n).Models assignment ↔ (view 0).Models assignment := by
 rcases GeneralDictionaryFiniteView257.two_views n with equal | equal
 · rw [equal]
 · rw [equal]; exact one_iff_zero assignment

theorem initial_public_models (n : Nat) (boundary : Assignment) :
 (∃ internal, GeneralDictionaryInitialProjection257.Agree internal boundary ∧
   GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context n).state internal) ↔
 (∃ internal, GeneralDictionaryInitialProjection257.Agree internal boundary ∧
   GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context 0).state internal) := by
 rw [GeneralDictionaryInitialProjection257.public_models,GeneralDictionaryInitialProjection257.public_models]
 apply exists_congr
 intro internal
 exact and_congr Iff.rfl (all_iff_zero n internal)
end Yulang.GeneralDictionaryNoModelRefinement257
