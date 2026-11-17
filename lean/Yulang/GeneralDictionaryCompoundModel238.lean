import Yulang.GeneralDictionaryCompoundPacket238
import Yulang.GeneralDictionaryDefaultPacketSupport213
import Yulang.GeneralNominalCenteredModelExtension
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundModel238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundPacket238
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
abbrev names (index : Fin 3) := fresh snapshot.seed root.identity declaration.id
  (if index.val = 0 then 3 else if index.val = 1 then 4 else 9) 0 0
abbrev values (index : Fin 3) : Ty := variant 0
  (if index.val = 0 then GeneralDictionaryOptionalOutput229.value else .emptyRecord)
noncomputable def extended : Assignment := GeneralNominalCenteredModelExtension.assign model names values
abbrev pool := [0,1,2,3,4,lo,hi,actual]
theorem fresh_outside (index : Fin 3) : names index ∉ pool := by
  have high : 4 < names index := GeneralNominalIdentities.source_above_seed _ _
  have separate (purpose : Nat) (different : (if index.val = 0 then 3 else if index.val = 1 then 4 else 9) ≠ purpose) :
      names index ≠ fresh snapshot.seed root.identity declaration.id purpose 0 0 :=
    GeneralNominalCenteredAllocation.fresh_namespaces different
  intro member
  simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h | h | h | h
  all_goals first | omega | exact separate _ (by split <;> (try split) <;> omega) h

theorem fresh_value (index : Fin 3) : (extended (names index)).1 = values index := by
  apply GeneralNominalCenteredModelExtension.assign_value
  intro first last equal
  have cases3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
    have h := i.isLt
    have h' : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases h' with h' | h' | h'
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Or.inl (Fin.ext h'))
    · exact Or.inr (Or.inr (Fin.ext h'))
  rcases cases3 first with rfl | rfl | rfl
  all_goals rcases cases3 last with rfl | rfl | rfl
  all_goals first | rfl | (exfalso; exact GeneralNominalCenteredAllocation.fresh_namespaces (by decide) equal)

theorem old_value (name : Nat) (member : name ∈ pool) : extended name = model name :=
  GeneralNominalCenteredModelExtension.assign_outside model names values
    (fun index same => fresh_outside index (same ▸ member))

theorem head_model : GeneralNominalCenteredHeadCandidates.HeadModels registry context root declaration [(0,0)] extended := by
  apply (GeneralDictionaryDefaultPacketSupport213.head_iff plan (first := model) (last := extended) ?_).mp GeneralDictionaryCompoundPacket238.head_model
  intro name member
  exact (old_value name ((by decide +kernel : GeneralDictionaryDefaultPacketSupport213.headSources plan ⊆ pool) member)).symm

theorem head_holds : plan.SchemaHolds plan.headSchema extended := by
  apply (GeneralNominalModeFrame181.schema_iff plan plan.headSchema (first := model) (last := extended) ?_).mp GeneralDictionaryCompoundPacket238.head_holds
  intro name member
  exact (old_value name ((by decide +kernel : GeneralNominalModeFrame181.schemaSources plan plan.headSchema ⊆ pool) member)).symm

theorem source_model : GeneralNominalState.Models snapshot extended :=
  (GeneralNominalAllocation.propagate_models ..).mp ((GeneralNominalState.extend_models ..).mp head_model.1).1 |>.1

theorem inhabited : GeneralNominalCenteredHeadMatStepJournal.Models start extended :=
  (GeneralNominalCenteredHeadMatStepJournal.point_initial_models root_point).mpr source_model

end Yulang.GeneralDictionaryCompoundModel238
