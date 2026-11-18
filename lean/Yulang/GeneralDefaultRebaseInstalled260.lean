import Yulang.GeneralDefaultRebaseModels260
namespace Yulang.GeneralDefaultRebaseInstalled260
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 (current)
open GeneralDictionaryVersionedGap206Install233 (effect installed)
open GeneralNominalCommonBridge (Assignment)

theorem installation (assignment : Assignment)
 (source : GeneralNominalVersionedJournal232.Models current assignment)
 (classes : GeneralNominalVersionedEffects231.ClassEffects current.core root plan assignment) :
 GeneralNominalVersionedInstall232.InstallationModels current effect assignment := by
 have packet := GeneralDictionaryVersionedGap206233.packet_holds assignment source
 refine ⟨source,packet,⟨GeneralNominalVersionedPlans231.head_models packet,classes⟩,?_,?_,?_⟩
 · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
     (fun _ => GeneralNominalVersionedTerminal232.requests_iff GeneralDictionaryVersionedGap206233.children_empty)).mpr classes
 · intro prior member; cases member
 · intro prior member; cases member

theorem installed_exact (assignment : Assignment) :
 GeneralNominalVersionedJournal232.Models installed assignment ↔
 GeneralNominalVersionedJournal232.Models current assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects current.core root plan assignment := by
 constructor
 · intro valid
   have before := (GeneralNominalVersionedInstall232.install_models (effect := effect) rfl).mp valid
   exact ⟨before.1,before.2.2.1.2⟩
 · rintro ⟨source,classes⟩
   exact (GeneralNominalVersionedInstall232.install_models rfl).mpr (installation assignment source classes)

theorem same_assignment (assignment : Assignment) :
 GeneralDefaultRebaseModels260.Models GeneralDefaultRebaseSource260.finalState assignment ↔
 GeneralNominalVersionedJournal232.Models installed assignment :=
 (GeneralDefaultRebaseModels260.final_exact assignment).trans (installed_exact assignment).symm

theorem evidence (assignment : Assignment)
 (valid : GeneralDefaultRebaseModels260.Models GeneralDefaultRebaseSource260.finalState assignment) :
 GeneralNominalVersionedEvidence231.Evidence registry current.core assignment root (.node 37 []) := by
 obtain ⟨source,classes⟩ := (GeneralDefaultRebaseModels260.final_exact assignment).mp valid
 apply GeneralNominalVersionedEvidence231.evidence_leaf
 refine ⟨plan,?_⟩
 exact GeneralNominalVersionedEvidence231.certificate_of_semantics GeneralDictionaryVersionedGap206233.frame
   GeneralDictionaryVersionedGap206233.children_empty.symm
   (GeneralDictionaryVersionedGap206233.packet_holds assignment source)
   GeneralDictionaryDefaultGap206State.ready classes

theorem counter_removed :
 GeneralDefaultRebaseModels260.Models GeneralDefaultRebaseSource260.initialState counter ∧
 ¬ GeneralDefaultRebaseModels260.Models GeneralDefaultRebaseSource260.finalState counter :=
 ⟨(GeneralDefaultRebaseModels260.initial_exact counter).mpr GeneralDictionaryVersionedGap206Install233.counter_model,
 fun final => GeneralDictionaryVersionedGap206Install233.bottom_removed ((same_assignment counter).mp final)⟩
end Yulang.GeneralDefaultRebaseInstalled260
