import Yulang.GeneralRebaseCompiledEvidenceAt282
import Yulang.GeneralDictionaryMixedGap206Stable234
import Yulang.GeneralDictionaryMixedGround218FinalOutcome235
import Yulang.GeneralRebaseStoredRegression280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseCompiledFixtures282
open GeneralRebaseCompiledEvidenceAt282 (EvidenceAt equivalent_at)
open GeneralRebaseWholeRow282 (Projection initialNames initial_projection)
open GeneralRebaseHistoryOrder282 (history decode)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralRebaseWholeJournal282 (View)
open GeneralRebasePrivateStore282 (Joint)
open GeneralRebaseTermCopy281 (Respects)
open GeneralRebaseLiveStore282 (live)

namespace Default
open GeneralDictionaryDefaultGap206Source (root registry model)
open GeneralDictionaryMixedGap206Refresh234 (refreshed reachable model_retained)

theorem selected_preserved : EvidenceAt registry refreshed root :=
  (equivalent_at reachable).mpr GeneralDictionaryMixedGap206Selected234.evidenceAt

theorem compiled_default :
    Projection (initialNames (raw refreshed).seed)
      (fun a => View refreshed (GeneralNominalCenteredHeadAllocEncoding.registry registry) root (.node 37 []) a ∧
        Respects (live refreshed) a) model := by
  apply (initial_projection reachable _ root (.node 37 []) model).mpr
  exact ⟨model,⟨fun _ _ => rfl,fun _ => rfl⟩,model_retained,
    GeneralDictionaryMixedGap206Evidence234.evidence model model_retained⟩

end Default

namespace Ground
open GeneralDictionaryGroundCopy218Source (root sourceRegistry)
open GeneralDictionaryMixedGround218FinalState235 (finalState reachable)
open GeneralDictionaryMixedGround218Leaf235 (oldChild)

theorem selected_preserved : EvidenceAt sourceRegistry finalState root :=
  (equivalent_at reachable).mpr GeneralDictionaryMixedGround218FinalRegression235.evidenceAt

theorem rejection_still_selected_as_rejected :
    GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry finalState oldChild .rejected ∧
    EvidenceAt sourceRegistry finalState root :=
  ⟨GeneralDictionaryMixedGround218FinalRejection235.rejected,selected_preserved⟩

end Ground

namespace Display
open GeneralNominalExamples (registry displayRoot model)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (after compiled)
open GeneralRebaseDisplayStep276 (initial_source)
open GeneralRebaseStoredRegression280 (stage)

theorem reached : GeneralNominalVersionedMixedProgressSplit236.Reachable registry displayRoot after :=
  ⟨before,initial_source,stage⟩

theorem selected_preserved : EvidenceAt registry after displayRoot :=
  (equivalent_at reached).mpr GeneralRebaseCompiledEvidenceAt277.evidenceAt

theorem compiled_nonleaf (outer : GeneralNominalCommonBridge.Assignment)
    (given : GeneralNominalVersionedJournal232.Models after outer) :
    Projection (initialNames (raw after).seed)
      (fun a => View after compiled displayRoot (.node 1 [.node 3 []]) a ∧ Respects (live after) a) outer :=
  (initial_projection reached compiled displayRoot (.node 1 [.node 3 []]) outer).mpr
    ⟨outer,⟨fun _ _ => rfl,fun _ => rfl⟩,given,GeneralRebaseCompiledEvidence277.real_nonleaf outer given⟩

end Display

end Yulang.GeneralRebaseCompiledFixtures282
