import Yulang.GeneralDeclarativeStoppedDiagnostic341
import Yulang.GeneralDeclarativeStoppedDepthProjection341
import Yulang.GeneralDeclarativeStoppedObstruction341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 16500000
namespace Yulang.GeneralDeclarativeStoppedReports341
open GeneralNominalVersionedMixedSourceBoundary234 (Local local_functional)
open GeneralDeclarativeStoppedDiagnostic341 (CurrentEdges from_packets replay_exact)
open CommonRoleOutermostResolver (Resolves Summarizes)

namespace Compound
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry declaration leaf)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundChildSite316 (child)
open GeneralLiveCompoundStable316 (reached_cases)
open GeneralLiveCompoundPost316 (generated_after)
open GeneralLiveCompoundFullResult316 (dictionary)
open GeneralDeclarativeStoppedObstruction341 (not_produces)
open GeneralDeclarativeStoppedFold340 (Produces)

theorem real_edges : CurrentEdges sourceRegistry after root := by
  intro here present key kids chosen generated member
  rcases reached_cases present with rfl|rfl
  · have same := local_functional chosen GeneralLiveCompoundPostRootSelect316.selected
    cases same
    cases List.mem_singleton.mp member
    exact generated_after
  · have same := local_functional chosen GeneralLiveCompoundPostLeafSelect316.selected
    cases same
    cases member

theorem recursive_report :
    Resolves (Local sourceRegistry after) root (.selected declaration.id [.selected leaf.id []]) ∧
    Summarizes (.selected declaration.id [.selected leaf.id []]) (.selected dictionary) ∧
    CurrentEdges sourceRegistry after root ∧ ¬ Produces sourceRegistry after root :=
  ⟨.selected GeneralLiveCompoundPostRootSelect316.selected
      (.cons (.selected GeneralLiveCompoundPostLeafSelect316.selected .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl),
    real_edges,not_produces⟩

end Compound

namespace Depth
open GeneralDictionaryOutputDepth252 (sourceRegistry root interpretation)
open GeneralRebaseDepthScalar285 (refreshed)
open GeneralDeclarativeStoppedDepth341 (terminal)
open GeneralDeclarativeStoppedDepthProjection341 (each placed)
open GeneralDeclarativeStoppedDepthWitness341 (current)
open GeneralDeclarativeStoppedDepthView341 (requested waiting)
open GeneralDeclarativeTaggedDictionary340 (Rule)

theorem report (done : Nat → Prop) :
    Resolves (Local sourceRegistry refreshed) root (.selected 0 []) ∧
    Resolves (Rule (current done) [] sourceRegistry interpretation waiting) requested (.selected 0 []) ∧
    Summarizes (.selected 0 []) (.selected (.node 0 [])) := by
  have raw : Resolves (Local sourceRegistry refreshed) root (.selected 0 []) :=
    .selected GeneralRebaseDepthHaltSelection285.selected .nil
  have summary : Summarizes (.selected 0 []) (.selected (.node 0 [])) :=
    .selected .nil (.selected rfl)
  exact ⟨raw,(replay_exact (from_packets terminal) (each done) raw summary).1,summary⟩

end Depth
end Yulang.GeneralDeclarativeStoppedReports341
