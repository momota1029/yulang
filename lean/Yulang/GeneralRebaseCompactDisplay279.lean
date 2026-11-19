import Yulang.GeneralRebaseCompactEdgeInstall279
import Yulang.GeneralRebaseInstallDisplayDelta279
import Yulang.GeneralRebaseCompiledEvidenceAt277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 8600000
namespace Yulang.GeneralRebaseCompactDisplay279
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (compiled parent effect after children)
open GeneralRebaseCompactEdgeInstall279 (reduced reduced_evidence reduced_models)
open GeneralRebaseEdgeReceipt279 (receipt freshEdges)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)

theorem exact_receipt : receipt before parent = [(displayRoot,displayChild)] := by
  change freshEdges [] (GeneralNominalVersionedChildren232.edges parent) = _
  unfold GeneralNominalVersionedChildren232.edges
  rw [children]
  rfl

theorem exact_reduced_edges :
    (reduced before effect).core.erased.current.edges = [(displayRoot,displayChild)] := by
  change [] ++ receipt before parent = _
  exact exact_receipt

theorem same_models (m : Assignment) : Models (reduced before effect) m ↔ Models before m :=
  (reduced_models before effect m).trans (GeneralRebaseCompiledInstall277.models m)

theorem actual_child :
    Generated (reduced before effect).core.erased.current displayRoot displayChild :=
  (GeneralRebaseCompactEdgeInstall279.reduced_generated before effect displayRoot displayChild).mpr
    GeneralRebaseInstallDisplayDelta279.generates_real_child.1

theorem actual_payload (m : Assignment) (valid : Models before m) :
    GeneralNominalVersionedEvidence231.Evidence compiled (reduced before effect).core m displayRoot
    (.node 1 [.node 3 []]) :=
  (reduced_evidence before effect compiled displayRoot m _).mpr
    (GeneralRebaseCompiledEvidence277.real_nonleaf m ((GeneralRebaseCompiledInstall277.models m).mpr valid))

end Yulang.GeneralRebaseCompactDisplay279
