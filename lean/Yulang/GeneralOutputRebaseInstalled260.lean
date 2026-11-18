import Yulang.GeneralOutputRebaseModels260
namespace Yulang.GeneralOutputRebaseInstalled260
open GeneralDictionaryOutputDepth252
open GeneralDictionaryOutputDepthInstall252 (effect installed)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

/-- Actual checked installation, with the very same assignment on both sides. -/
theorem installation (assignment : Assignment)
 (valid : GeneralNominalVersionedPlans231.Holds plan assignment) :
 GeneralNominalVersionedInstall232.InstallationModels initial effect assignment := by
 have classValid := GeneralDictionaryOutputCompletion258.classes assignment valid.2.2
 refine ⟨?_,valid,⟨GeneralNominalVersionedPlans231.head_models valid,classValid⟩,?_,?_,?_⟩
 · exact (GeneralNominalVersionedJournal232.initial_models ..).mpr
     ⟨valid.1,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩
 · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
     (fun _ => GeneralNominalVersionedTerminal232.requests_iff children_empty)).mpr classValid
 · intro prior member; cases member
 · intro prior member; cases member

theorem installed_packet (assignment : Assignment) :
 GeneralNominalVersionedJournal232.Models installed assignment ↔
 GeneralNominalVersionedPlans231.Holds plan assignment := by
 constructor
 · intro valid; exact valid.2.1 plan List.mem_cons_self
 · intro valid
   exact (GeneralNominalVersionedInstall232.install_models rfl).mpr (installation assignment valid)

theorem same_assignment (assignment : Assignment) :
 GeneralOutputRebaseModels260.Models GeneralOutputRebaseSource260.finalState assignment ↔
 GeneralNominalVersionedJournal232.Models installed assignment :=
 (GeneralOutputRebaseModels260.final_packet assignment).trans (installed_packet assignment).symm

theorem evidence (assignment : Assignment)
 (valid : GeneralOutputRebaseModels260.Models GeneralOutputRebaseSource260.finalState assignment) :
 GeneralNominalVersionedEvidence231.Evidence registry initial.core assignment root (.node 0 []) := by
 have packetValid := (GeneralOutputRebaseModels260.final_packet assignment).mp valid
 apply GeneralNominalVersionedEvidence231.evidence_leaf
 refine ⟨plan,?_⟩
 exact GeneralNominalVersionedEvidence231.certificate_of_semantics frame children_empty.symm
   packetValid GeneralDictionaryOutputDepthInstall252.ready
   (GeneralDictionaryOutputCompletion258.classes assignment packetValid.2.2)
end Yulang.GeneralOutputRebaseInstalled260
