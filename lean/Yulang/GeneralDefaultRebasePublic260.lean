import Yulang.GeneralDefaultRebaseCompletion260
namespace Yulang.GeneralDefaultRebasePublic260
open GeneralRebaseStep258
open GeneralDefaultRebaseSource260 (facts initialState finalState)
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 (current)
open GeneralDefaultRebaseCompletion260 (complete)
open GeneralNominalCommonBridge (Assignment)
open GeneralDefaultRebaseModels260 (Models)

def Agree (first last : Assignment) : Prop :=
 (∀ name, name ≠ 0 → first name = last name) ∧ (∀ name, (first name).2 = (last name).2)

theorem completion_agrees (assignment : Assignment) : Agree (complete assignment) assignment :=
 ⟨GeneralDefaultRebaseCompletion260.outside assignment,GeneralDefaultRebaseCompletion260.rows assignment⟩

theorem source_agree (first last : Assignment) (same : Agree first last) :
 GeneralNominalState.Models snapshot first ↔ GeneralNominalState.Models snapshot last :=
 GeneralDefaultRebaseCompletion260.source_iff first last same.2
   (fun name different => congrArg Prod.fst (same.1 name different))

theorem completed (state : State facts) (boundary : Assignment)
 (source : GeneralNominalState.Models snapshot boundary) : Models state (complete boundary) := by
 have final := GeneralDefaultRebaseCompletion260.final boundary source
 refine ⟨final.1,?_⟩
 intro fact member
 have inside : fact ∈ facts := (List.mem_filter.mp member).1
 have full : fact ∈ present finalState := by simpa [present,finalState,done] using inside
 exact final.2 fact full

theorem public_models (state : State facts) (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ Models state assignment) ↔
 GeneralNominalState.Models snapshot boundary := by
 constructor
 · rintro ⟨assignment,same,valid⟩
   exact (source_agree assignment boundary same).mp ((GeneralDefaultRebaseBody260.current_source assignment).mp valid.1)
 · intro source
   exact ⟨complete boundary,completion_agrees boundary,completed state boundary source⟩

structure Certificate (boundary : Assignment) : Prop where
 agrees : Agree (complete boundary) boundary
 current : GeneralNominalVersionedJournal232.Models GeneralDictionaryVersionedGap206233.current (complete boundary)
 packet : GeneralNominalVersionedPlans231.Holds plan (complete boundary)
 classes : GeneralNominalVersionedEffects231.ClassEffects GeneralDictionaryVersionedGap206233.current.core root plan (complete boundary)
 installed : GeneralNominalVersionedJournal232.Models GeneralDictionaryVersionedGap206Install233.installed (complete boundary)
 final : Models finalState (complete boundary)
 evidence : GeneralNominalVersionedEvidence231.Evidence registry GeneralDictionaryVersionedGap206233.current.core
   (complete boundary) root (.node 37 [])

theorem certificate (boundary : Assignment)
 (source : GeneralNominalState.Models snapshot boundary) : Certificate boundary := by
 have final := GeneralDefaultRebaseCompletion260.final boundary source
 obtain ⟨prior,classes⟩ := (GeneralDefaultRebaseModels260.final_exact _).mp final
 exact ⟨completion_agrees boundary,prior,GeneralDictionaryVersionedGap206233.packet_holds _ prior,
   classes,(GeneralDefaultRebaseInstalled260.same_assignment _).mp final,final,
   GeneralDefaultRebaseInstalled260.evidence _ final⟩

theorem run_certificate (boundary : Assignment)
 (source : GeneralNominalState.Models snapshot boundary) :
 GeneralDefaultRebaseRun260.run initialState = .ok (some finalState) ∧ Certificate boundary :=
 ⟨GeneralDefaultRebaseRun260.first,certificate boundary source⟩
end Yulang.GeneralDefaultRebasePublic260
