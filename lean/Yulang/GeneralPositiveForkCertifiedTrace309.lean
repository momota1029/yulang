import Yulang.GeneralCommittedReadTrace309
import Yulang.GeneralPositiveForkCheck309
import Yulang.GeneralPositiveForkPacked309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralPositiveForkCertifiedTrace309
open GeneralPositiveForkSource309 (registry root checked)
open GeneralPositiveForkInstall309 (after reachable inhabited)
open GeneralPositiveForkCompiler309 (read decode faithful)
open GeneralPositiveForkSettlement309 (committed_read)
open GeneralPositiveForkEvidence309 (payload)
open GeneralPositiveForkCheck309 (accepted)
open GeneralPositiveForkPacked309 (Joint exact_joint footprint)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDeclarationExamples (roles)
open GeneralOrderedDictionaryCheck309 (validate)
open GeneralCommittedReadTrace309 (Trace)
open GeneralRebasePackedAnswers298 (pack fill)

theorem exact_trace (m : Assignment) (valid : Models after m) :
    Trace registry after root m read decode 0 payload ∧
      (boundary roles).Evidence registry after m root payload :=
  (GeneralCommittedReadTrace309.verified ⟨rfl,checked⟩ reachable read decode committed_read faithful
    2 0 payload (.root) ((accepted 2 payload).mpr ⟨by decide,rfl⟩)).2 m valid

theorem packed_trace (m fallback : Assignment) (valid : Models after m) :
    let current := fill footprint (pack footprint m) fallback
    Joint current payload (.node 2 []) (.node 3 []) ∧ Trace registry after root current read decode 0 payload := by
  dsimp
  have j := (exact_joint m _ _ _).mpr
    ⟨(GeneralPositiveForkPacked309.model_exact _).mp valid,rfl,rfl,rfl⟩
  refine ⟨(GeneralPositiveForkPacked309.exact_packed m fallback _ _ _).mpr j,?_⟩
  exact (exact_trace _ ((GeneralPositiveForkPacked309.exact_packed m fallback _ _ _).mpr j).1).1

end Yulang.GeneralPositiveForkCertifiedTrace309
