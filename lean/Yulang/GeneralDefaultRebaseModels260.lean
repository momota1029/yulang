import Yulang.GeneralDefaultRebaseSource260
namespace Yulang.GeneralDefaultRebaseModels260
open GeneralRebaseStep258
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 (current)
open GeneralDefaultRebaseBody260 (body schema)
open GeneralDefaultRebaseSource260 (facts initialState finalState)
open GeneralNominalCommonBridge (Assignment)

def factHolds (assignment : Assignment) : Fact → Prop
 | .installed owner => owner = 37
 | .binder index => GeneralRebaseOwnedOutputKeys260.Holds 37 schema
     (GeneralNominalVersionedEffects231.bodyVariables plan assignment body) assignment (.binder index)
 | _ => False

def Models := GeneralRebaseFactSemantics259.Models (basis := facts)
 (GeneralNominalVersionedJournal232.Models current) factHolds

theorem output_meaning (assignment : Assignment) : factHolds assignment (.binder 1408) ↔
 GeneralNominalVersionedEffects231.ClassEffects current.core root plan assignment := by
 change GeneralRebaseOwnedOutputKeys260.Holds 37 schema
  (GeneralNominalVersionedEffects231.bodyVariables plan assignment body) assignment (.binder 1408) ↔ _
 have all := GeneralRebaseOwnedOutputKeys260.all_exact 37 schema
   (GeneralNominalVersionedEffects231.bodyVariables plan assignment body) assignment
 rw [GeneralDefaultRebaseSource260.output_keys] at all
 simp only [List.mem_singleton,forall_eq] at all
 exact all.trans ((GeneralDefaultRebaseBody260.body_meaning assignment).trans
   (GeneralDefaultRebaseBody260.classes_exact assignment).symm)

theorem initial_exact (assignment : Assignment) : Models initialState assignment ↔
 GeneralNominalVersionedJournal232.Models current assignment := GeneralRebaseFactSemantics259.initial_exact ..

theorem final_exact (assignment : Assignment) : Models finalState assignment ↔
 GeneralNominalVersionedJournal232.Models current assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects current.core root plan assignment := by
 rw [Models,GeneralRebaseFactSemantics259.done_exact]
 constructor
 · rintro ⟨source,all⟩
   exact ⟨source,(output_meaning assignment).mp (all (.binder 1408) (by simp [facts]))⟩
 · rintro ⟨source,outputs⟩
   refine ⟨source,?_⟩
   intro fact member
   rcases List.mem_cons.mp member with rfl | last
   · rfl
   · cases List.mem_singleton.mp last
     exact (output_meaning assignment).mpr outputs
end Yulang.GeneralDefaultRebaseModels260
