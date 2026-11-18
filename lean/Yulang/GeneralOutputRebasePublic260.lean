import Yulang.GeneralOutputRebaseRun260
namespace Yulang.GeneralOutputRebasePublic260
open GeneralRebaseStep258
open GeneralOutputRebaseSource260 (facts initialState finalState)
open GeneralDictionaryOutputDepth252
open GeneralDictionaryOutputFrame258 (complete)
open GeneralDictionaryOutputPublic258 (Agree)
open GeneralNominalCommonBridge (Assignment)
open GeneralOutputRebaseModels260 (Models)

/-- The designated output3 type is released; every other component and all
rows are fixed. This is not same-assignment preservation of every initial model. -/
theorem public_models (state : State facts) (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ Models state assignment) ↔
 GeneralNominalState.Models snapshot boundary := by
 constructor
 · rintro ⟨assignment,same,valid⟩
   exact (GeneralDictionaryOutputPublic258.source_agree assignment boundary same).mp valid.1
 · intro source
   exact ⟨complete boundary,GeneralDictionaryOutputPublic258.completion_agrees boundary,
     GeneralOutputRebaseModels260.completed state boundary source⟩

theorem installed_public (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧
 GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepthInstall252.installed assignment) ↔
 (∃ assignment, Agree assignment boundary ∧ Models finalState assignment) := by
 constructor
 · rintro ⟨assignment,same,valid⟩
   exact ⟨assignment,same,(GeneralOutputRebaseInstalled260.same_assignment assignment).mpr valid⟩
 · rintro ⟨assignment,same,valid⟩
   exact ⟨assignment,same,(GeneralOutputRebaseInstalled260.same_assignment assignment).mp valid⟩

structure Certificate (boundary : Assignment) : Prop where
 agrees : Agree (complete boundary) boundary
 initial : GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepth252.initial (complete boundary)
 packet : GeneralNominalVersionedPlans231.Holds plan (complete boundary)
 installed : GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepthInstall252.installed (complete boundary)
 final : Models finalState (complete boundary)
 evidence : GeneralNominalVersionedEvidence231.Evidence registry GeneralDictionaryOutputDepth252.initial.core
   (complete boundary) root (.node 0 [])

theorem certificate (boundary : Assignment)
 (source : GeneralNominalState.Models snapshot boundary) : Certificate boundary := by
 have final := GeneralOutputRebaseModels260.completed finalState boundary source
 have packet := (GeneralOutputRebaseModels260.final_packet _).mp final
 refine ⟨GeneralDictionaryOutputPublic258.completion_agrees boundary,?_,packet,
   (GeneralOutputRebaseInstalled260.same_assignment _).mp final,final,
   GeneralOutputRebaseInstalled260.evidence _ final⟩
 exact (GeneralNominalVersionedJournal232.initial_models ..).mpr
   ⟨packet.1,fun _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩

theorem run_certificate (boundary : Assignment)
 (source : GeneralNominalState.Models snapshot boundary) :
 GeneralOutputRebaseRun260.run initialState = .ok (some finalState) ∧ Certificate boundary :=
 ⟨GeneralOutputRebaseRun260.first,certificate boundary source⟩

theorem requested_output_exact (output : CommonNominalFullCarrier.Ty) :
 Models finalState (GeneralDictionaryPendingOutput258.replace output) ↔
 CommonNominalFullCarrier.Equivalent output P := by
 rw [GeneralOutputRebaseModels260.final_exact]
 exact (and_iff_right (GeneralDictionaryPendingOutput258.source_models output)).trans
   (GeneralDictionaryPendingOutput258.outputs_exact output)
end Yulang.GeneralOutputRebasePublic260
