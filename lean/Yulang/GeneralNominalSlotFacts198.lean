import Yulang.GeneralNominalSlotReport198
import Yulang.GeneralDictionaryRefinedLocations

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalSlotFacts198
open GeneralNominalState (State)
open GeneralNominalRecursiveInspection
open GeneralNominalRefinements (Refines)
open GeneralNominalSlotObservation198 (bounds)
open GeneralNominalSlotReport198 (report capture)
variable {before after : State}

theorem bindings_report (refinement : Refines before after) (item : Report before) :
    bindings after (report refinement.base.embed item) = bindings before item := by
  simp [bindings,report,capture,bounds,List.map_map,refinement.base.source]

theorem selfChecks_report (refinement : Refines before after) (item : Report before) :
    selfChecks after (report refinement.base.embed item) = selfChecks before item := by
  simp [selfChecks,report,bounds,List.map_map,refinement.base.source]

theorem finished_report (embed : Fin before.base.slots → Fin after.base.slots) (item : Report before) :
    Finished (report embed item) ↔ Finished item := by
  simp [Finished,report]

theorem projection_report (refinement : Refines before after) (item : Report before)
    (model : GeneralNominalCommonBridge.Assignment) :
    ProjectionModels after (report refinement.base.embed item) model ↔ ProjectionModels before item model := by
  simp only [ProjectionModels,report,List.forall_mem_map,capture,Fits,bounds,refinement.base.source]

theorem materialization_report (refinement : Refines before after) (item : Report before)
    (declaration : GeneralDeclarations.Declaration) (captured : GeneralDeclarationDemands.Capture)
    (schema : GeneralNominalMaterialization.Schema) (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalMaterialization.Models after declaration captured (report refinement.base.embed item) schema model ↔
      GeneralNominalMaterialization.Models before declaration captured item schema model := by
  simp [GeneralNominalMaterialization.Models,report,capture]

variable {old next : GeneralNominalCandidates.Context}

theorem candidate_report (refinement : Refines old.state next.state)
    (interpretation : next.interpretation = old.interpretation)
    (observed : GeneralNominalRefinementTrace197.ObservedMany old.state
      (GeneralNominalInspection.queries old.state old.interpretation declaration) pairs) :
    GeneralNominalRecursiveCandidates.report next declaration (pairs.map (bounds refinement.base.embed)) =
      report refinement.base.embed (GeneralNominalRecursiveCandidates.report old declaration pairs) := by
  unfold GeneralNominalRecursiveCandidates.report
  have queries : GeneralNominalInspection.queries next.state next.interpretation declaration =
      GeneralNominalInspection.queries old.state old.interpretation declaration := by
    simp only [GeneralNominalInspection.queries,interpretation,refinement.constructors]
  rw [queries,GeneralNominalSlotReport198.inspectMany_report refinement observed]
  simp [report,List.map_append]
end Yulang.GeneralNominalSlotFacts198
