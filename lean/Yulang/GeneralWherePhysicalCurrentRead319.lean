import Yulang.GeneralWherePhysicalReobserve319
import Yulang.GeneralWherePhysicalActive319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 27000000
namespace Yulang.GeneralWherePhysicalCurrentRead319
open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleRead318 (firstOrigin secondOrigin new_report new_query new_reads)
open GeneralWhereOriginSingleCells318 (loNow hi lower_moves upper_kept sig)
open GeneralWherePhysicalPast319 (point pointCtx two savedHi)
open GeneralWherePhysicalIndex319 (old)
open GeneralWherePhysicalReobserve319 (updated updated_model)
open GeneralWherePhysicalFresh319 (old_lookup_absent)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot interpretation)
open GeneralDictionaryJournalRefinement228Reobserve (exactCopy)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalRecursiveCandidates (report arguments)
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalReportErasure (erase interval)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralVersionedEndpointAddress315 (atCell)
open GeneralWhereVersionCase317 (expr)
open GeneralWhereOriginDelta318 (Cell)
open GeneralNominalVersionedExpressionFrame236 (variableSource)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)

abbrev zero : Fin 7 := old 2 (0 : Fin 5)
abbrev desc : GeneralNominalState.Descriptor 7 :=
  GeneralNominalRefinements.renameDescriptor (old 2) exactCopy

abbrev packet : Packet roles :=
  ⟨registry,pointCtx,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(zero,zero)]⟩

abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩

theorem locate : arguments pointCtx (inputs root) = some [(zero,zero)] := by
  change GeneralCandidateBoundaryParts.locate point.base [(0,0)] = _
  have good : sourceSlot point.base 0 = some zero := (sourceSlot_exact ..).mpr rfl
  simp only [GeneralCandidateBoundaryParts.locate,List.mapM_cons,good]
  rfl

theorem query : GeneralNominalInspection.queries point interpretation declaration =
    [.nominal 0 [.variables [0],.variables [1]]] := new_query

theorem nominal0 : point.nominals zero = some desc := rfl

theorem exact_report : report pointCtx declaration [(zero,zero)] =
    { inspected := [(zero,zero)], checked := [(zero,zero),(zero,zero),(two,two),(two,two)],
      captures := [⟨0,(two,two),some firstOrigin⟩,⟨1,(two,two),some secondOrigin⟩],
      anchors := [(firstOrigin,(two,two)),(secondOrigin,(two,two))] } := by
  have tag : desc.declaration.name = 0 := rfl
  have rawId : point.base.source zero = 0 := rfl
  have sub : inspectMany point [.variables [0],.variables [1]] [(two,two),(two,two)]
      (fun i => some (.nominal (.source 0) 0 i)) 0 =
      { captures := [⟨0,(two,two),some firstOrigin⟩,⟨1,(two,two),some secondOrigin⟩],
        checked := [(two,two),(two,two)],anchors := [(firstOrigin,(two,two)),(secondOrigin,(two,two))] } := by
    simp [inspectMany,inspect,Report.append,firstOrigin,secondOrigin]
  unfold report
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit,nominal0,tag,rawId]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem same : Same newPlan plan := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  change erase GeneralLiveCompoundUpperSnapshot316.snap
    (report GeneralLiveCompoundUpperSnapshot316.context declaration [((0 : Fin 8),0)]) =
    erase point (report pointCtx declaration [(zero,zero)])
  rw [new_report,exact_report]
  rfl

theorem bindings : packet.bindings = [(0,2,2),(1,2,2)] :=
  (GeneralNominalCenteredHeadMatPlanData.bindings same).symm.trans GeneralWhereOriginSingleRead318.new_bindings

theorem reads : variableSource plan .lower 0 = 2 ∧ variableSource plan .upper 0 = 2 :=
  ⟨(GeneralWhereVersionRecompile317.variable_eq same .lower 0).symm.trans new_reads.1,
    (GeneralWhereVersionRecompile317.variable_eq same .upper 0).symm.trans new_reads.2⟩

theorem address_lo : atCell plan .lower otherChild.id 0 expr = loNow :=
  (GeneralWhereVersionRecompile317.address same .lower otherChild.id 0 expr).symm
theorem address_hi : atCell plan .upper otherChild.id 0 expr = hi :=
  (GeneralWhereVersionRecompile317.address same .upper otherChild.id 0 expr).symm.trans upper_kept

abbrev low : Cell plan :=
  ⟨otherChild,0,.lower,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,(fun _ eq => by cases eq),rfl⟩
abbrev high : Cell plan :=
  ⟨otherChild,0,.upper,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,(fun _ eq => by cases eq),rfl⟩

theorem child_bounds :
    (GeneralWhereVersionCompiler317.child plan otherChild sig).occurrence.demand.arguments 0 = (loNow,hi) := by
  have e := GeneralWhereOriginDescriptor318.argument (p := plan) sig 0
      (pat := .variant 0 (.var 0)) rfl (fun _ eq => by cases eq) (expr := expr) rfl
  change _ = (atCell plan .lower otherChild.id 0 expr,atCell plan .upper otherChild.id 0 expr) at e
  rwa [address_lo,address_hi] at e

end Yulang.GeneralWherePhysicalCurrentRead319
