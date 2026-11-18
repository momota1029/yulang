import Yulang.GeneralOutputRebaseSource260
namespace Yulang.GeneralOutputRebaseModels260
open GeneralRebaseStep258
open GeneralOutputRebaseSource260 (facts initialState finalState schema)
open GeneralDictionaryOutputDepth252
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def factHolds (assignment : Assignment) : Fact → Prop
 | .lower owner atom => owner = 0 ∧ atom = 0 ∧ Subtype (assignment 2).1 (assignment 2).1
 | .upper owner atom => owner = 0 ∧ atom = 0 ∧ Subtype (assignment 2).1 (assignment 2).1
 | .binder 0 => Subtype (assignment 2).1 (assignment 2).1
 | .binder 1 => Subtype (assignment 2).1 (assignment 2).1
 | .binder index => GeneralRebaseOutputKeys260.Holds 2 schema
     (GeneralNominalVersionedPlans231.variables plan assignment) assignment (.binder index)
 | .installed owner => owner = 0

def Models := GeneralRebaseFactSemantics259.Models (basis := facts) (GeneralNominalState.Models snapshot) factHolds

theorem output_meaning (assignment : Assignment) : factHolds assignment (.binder 2) ↔
 GeneralNominalVersionedPlans231.Outputs plan assignment := by
 change GeneralRebaseOutputKeys260.Holds 2 schema
  (GeneralNominalVersionedPlans231.variables plan assignment) assignment (.binder 2) ↔
  schema.Holds (GeneralNominalVersionedPlans231.variables plan assignment) assignment
 rw [← GeneralRebaseOutputKeys260.all_exact 2 schema,GeneralOutputRebaseSource260.output_keys]
 simp only [List.mem_singleton,forall_eq]

theorem initial_exact (assignment : Assignment) : Models initialState assignment ↔
 GeneralNominalState.Models snapshot assignment := GeneralRebaseFactSemantics259.initial_exact ..

theorem final_exact (assignment : Assignment) : Models finalState assignment ↔
 GeneralNominalState.Models snapshot assignment ∧ GeneralNominalVersionedPlans231.Outputs plan assignment := by
 rw [Models,GeneralRebaseFactSemantics259.done_exact]
 constructor
 · rintro ⟨source,all⟩
   exact ⟨source,(output_meaning assignment).mp (all (.binder 2) (by simp [facts]))⟩
 · rintro ⟨source,outputs⟩
   refine ⟨source,?_⟩
   intro fact member
   simp only [facts,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl
   · rfl
   · exact ⟨rfl,rfl,subtype_refl _⟩
   · exact ⟨rfl,rfl,subtype_refl _⟩
   · exact subtype_refl _
   · exact subtype_refl _
   · exact (output_meaning assignment).mpr outputs

/-- The full actual packet judgement, not merely syntactic decoder acceptance. -/
theorem final_packet (assignment : Assignment) : Models finalState assignment ↔
 GeneralNominalVersionedPlans231.Holds plan assignment :=
 (final_exact assignment).trans (GeneralDictionaryOutputInputs258.packet_exact assignment).symm

theorem completed (state : State facts) (assignment : Assignment)
 (source : GeneralNominalState.Models snapshot assignment) :
 Models state (GeneralDictionaryOutputFrame258.complete assignment) := by
 have final := (final_packet _).mpr ((GeneralDictionaryOutputCompletion258.packet_exact assignment).mpr source)
 refine ⟨final.1,?_⟩
 intro fact member
 have inside : fact ∈ facts := (List.mem_filter.mp member).1
 have full : fact ∈ present finalState := by simpa [present,finalState,done] using inside
 exact final.2 fact full

theorem bad_initial_not_final :
 Models initialState (GeneralDictionaryPendingOutput258.replace .bottom) ∧
 ¬ Models finalState (GeneralDictionaryPendingOutput258.replace .bottom) := by
 refine ⟨(initial_exact _).mpr (GeneralDictionaryPendingOutput258.source_models .bottom),?_⟩
 intro final
 exact GeneralDictionaryOutputPremise258.initial_not_packet.2 ((final_packet _).mp final)
end Yulang.GeneralOutputRebaseModels260
