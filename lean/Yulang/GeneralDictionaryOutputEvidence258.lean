import Yulang.GeneralDictionaryOutputCompletion258
namespace Yulang.GeneralDictionaryOutputEvidence258
open GeneralDictionaryOutputDepth252
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryOutputFrame258 (complete)

theorem no_initial_evidence (payload : GeneralDictionaryReadback.Payload) :
 ¬ GeneralNominalVersionedEvidence231.Evidence registry initial.core
   (GeneralDictionaryPendingOutput258.replace .bottom) root payload := by
 rintro ⟨tree,⟨rootEq,_⟩,valid⟩
 cases tree with
 | node focus key children =>
   change focus = root at rootEq
   subst focus
   cases valid with
   | node rule _ =>
     obtain ⟨candidate,certificate⟩ := rule
     have same := GeneralDictionaryOutputDepthInstall252.frame_plan certificate.frame
     rw [same] at certificate
     exact GeneralDictionaryOutputPremise258.initial_not_packet.2 certificate.packet

/-- The fixed checked leaf source has evidence after explicit output completion;
this is not a producer for arbitrary source configurations or children. -/
theorem completed_evidence (assignment : Assignment) (source : GeneralNominalState.Models snapshot assignment) :
 GeneralNominalVersionedEvidence231.Evidence registry initial.core (complete assignment) root (.node 0 []) := by
 apply GeneralNominalVersionedEvidence231.evidence_leaf
 refine ⟨plan,?_⟩
 exact GeneralNominalVersionedEvidence231.certificate_of_semantics frame children_empty.symm
   ((GeneralDictionaryOutputCompletion258.packet_exact assignment).mpr source)
   GeneralDictionaryOutputDepthInstall252.ready
   (GeneralDictionaryOutputCompletion258.classes (complete assignment)
     (GeneralDictionaryOutputCompletion258.completed_outputs assignment))
end Yulang.GeneralDictionaryOutputEvidence258
