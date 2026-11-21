import Yulang.GeneralWherePhysicalCommit319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 35000000
namespace Yulang.GeneralWherePhysicalChildRead319
open GeneralWhereOriginSingleSource318 (registry)
open GeneralWherePhysicalCommit319 (final newChild)
open GeneralWherePhysicalCurrentRead319 (child_bounds)
open GeneralWherePhysicalFresh319 (lowerSlot upperSlot oldTwo final_slots)
open GeneralWherePhysicalActive319 (active ctx view heads shapes)
open GeneralWhereOriginSingleCells318 (loNow hi)
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralLiveCompoundRegistry316 (leaf leaf_checked)
open GeneralNominalCenters
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedCandidates231 (inputs)

noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,ctx,newChild.observed,leaf,leaf_checked,[(lowerSlot,upperSlot)]⟩

noncomputable abbrev plan : Plan roles := ⟨packet,newChild,rfl⟩

theorem locate : arguments ctx (inputs newChild.occurrence) = some [(lowerSlot,upperSlot)] := by
  change GeneralCandidateBoundaryParts.locate active.base
    (List.ofFn (inputs newChild.occurrence).demand.arguments) = _
  have single : List.ofFn (inputs newChild.occurrence).demand.arguments = [(loNow,hi)] := by
    rw [List.ofFn_succ]
    have p : (inputs newChild.occurrence).demand.arguments 0 = (loNow,hi) := child_bounds
    rw [p]
    rfl
  rw [single]
  have a : GeneralDictionaryBinderLocations.sourceSlot active.base hi = some upperSlot := final_slots.1
  have b : GeneralDictionaryBinderLocations.sourceSlot active.base loNow = some lowerSlot := final_slots.2
  simp only [GeneralCandidateBoundaryParts.locate,List.mapM_cons,a,b]
  rfl

theorem query : GeneralNominalInspection.queries active ctx.interpretation leaf =
    [.node (.variant 0) [.variables [0]]] :=
  GeneralLiveCompoundChildSite316.leaf_query

theorem actual_report : report ctx leaf [(lowerSlot,upperSlot)] =
    { inspected := [(lowerSlot,upperSlot)],
      checked := [(lowerSlot,upperSlot),(lowerSlot,upperSlot),(oldTwo,oldTwo)],
      captures := [⟨0,(oldTwo,oldTwo),none⟩] } := by
  have sub : inspectMany active [.variables [0]] [(oldTwo,oldTwo)] (fun _ => none) 0 =
      {captures := [⟨0,(oldTwo,oldTwo),none⟩],checked := [(oldTwo,oldTwo)]} := by
    rw [inspectMany.eq_2,inspectMany.eq_1]
    simp only [inspect.eq_1,Report.append]
    rfl
  have a : active.view.heads lowerSlot = .structural (1 : Fin 2) (fun _ => oldTwo) := rfl
  have b : active.view.heads upperSlot = .structural (1 : Fin 2) (fun _ => oldTwo) := rfl
  have tag : active.view.shapes (1 : Fin 2) = .variant 0 := rfl
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append,a,b,tag]

theorem binding : packet.bindings = [(0,2,2)] := by
  change bindings active (report ctx leaf [(lowerSlot,upperSlot)]) = _
  rw [actual_report]
  change [(0,active.base.source oldTwo,active.base.source oldTwo)] = _
  rw [show active.base.source oldTwo = 2 from GeneralWherePhysicalFresh319.oldTwo_id]

theorem finished : Finished (report ctx leaf [(lowerSlot,upperSlot)]) := by
  rw [actual_report]
  exact ⟨rfl,rfl,rfl⟩

end Yulang.GeneralWherePhysicalChildRead319
