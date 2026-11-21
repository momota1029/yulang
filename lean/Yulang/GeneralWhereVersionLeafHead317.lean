import Yulang.GeneralWhereVersionCommit317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 36000000
namespace Yulang.GeneralWhereVersionLeafHead317
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralLiveCompoundRegistry316 (registry leaf leaf_checked)
open GeneralWhereVersionBase317 (loSlot hiSlot two injectOld source source_old source_lo source_hi)
open GeneralWhereVersionCase317 (site occ lower upper descriptor)
open GeneralWhereVersionSnapshot317 (snap context)
open GeneralWhereVersionCommit317 (ports new_snapshot)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralNominalCenters
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedPlans231 (Ordinary HeadModels)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,site.observed,leaf,leaf_checked,[(loSlot,hiSlot)]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,site,rfl⟩

theorem located : arguments context (inputs occ) = some [(loSlot,hiSlot)] := by
  change GeneralCandidateBoundaryParts.locate snap.base (List.ofFn (inputs occ).demand.arguments) = _
  have slots : List.ofFn (inputs occ).demand.arguments = [(lower,upper)] := by
    rw [List.ofFn_succ]
    have zero : (inputs occ).demand.arguments 0 = (lower,upper) := descriptor
    rw [zero]
    rfl
  rw [slots]
  unfold GeneralCandidateBoundaryParts.locate
  have a := (GeneralDictionaryBinderLocations.sourceSlot_exact snap.base lower loSlot).mpr source_lo
  have b := (GeneralDictionaryBinderLocations.sourceSlot_exact snap.base upper hiSlot).mpr source_hi
  simp only [List.mapM_cons,a,b]
  rfl

theorem query : GeneralNominalInspection.queries snap context.interpretation leaf =
    [.node (.variant 0) [.variables [0]]] :=
  GeneralLiveCompoundChildSite316.leaf_query

theorem report_exact : report context leaf [(loSlot,hiSlot)] =
    { inspected := [(loSlot,hiSlot)], checked := [(loSlot,hiSlot),(loSlot,hiSlot),(two,two)],
      captures := [⟨0,(two,two),none⟩] } := by
  have sub : inspectMany snap [.variables [0]] [(two,two)] (fun _ => none) 0 =
      {captures := [⟨0,(two,two),none⟩],checked := [(two,two)]} := by
    rw [inspectMany.eq_2,inspectMany.eq_1]
    simp only [inspect.eq_1,Report.append]
    rfl
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem binding : packet.bindings = [(0,2,2)] := by
  change bindings snap (report context leaf [(loSlot,hiSlot)]) = _
  rw [report_exact]
  change [(0,source two,source two)] = _
  rw [source_old]
  rfl

theorem capture : (GeneralNominalVersionedFrame231.capture packet).inputs 0 = (2,2) := by
  change (GeneralNominalVersionedAllocation231.capture snap registry occ.identity leaf.id packet.bindings).inputs 0 = _
  rw [binding]; rfl

theorem binder : GeneralNominalVersionedFrame231.binder plan 0 = 2 := by
  unfold GeneralNominalVersionedFrame231.binder
  change (if (0:Nat) ∈ leaf.outputNames then _ else if
    ((GeneralNominalVersionedFrame231.capture packet).inputs 0).1 =
    ((GeneralNominalVersionedFrame231.capture packet).inputs 0).2 then _ else _) = _
  simp [capture,show (0:Nat) ∉ leaf.outputNames from by decide]

theorem ordinary (m : Assignment) (valid : ParentHolds m) : Ordinary packet m := by
  refine ⟨?_,?_,?_⟩
  · rw [binding]
    intro a ha b hb _
    cases List.mem_singleton.mp ha
    cases List.mem_singleton.mp hb
    exact subtype_refl _
  · unfold GeneralNominalVersionedAllocation231.merges
    rw [binding]
    exact PresenceNormalForm.all_nil _ _
  · change PresenceNormalForm.All CommonNominalFullCarrier.model m
      (selfChecks snap (report context leaf [(loSlot,hiSlot)]))
    rw [report_exact]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    have fits : Subtype (m (source loSlot)).1 (m (source hiSlot)).1 := by
      rw [source_lo,source_hi]
      exact subtype_trans (ports m valid).1.1 (ports m valid).2.2
    rcases member with rfl|rfl|rfl
    · exact fits
    · exact fits
    · exact subtype_refl _

theorem projections (m : Assignment) : ProjectionModels snap (GeneralNominalPacketSupport.report packet) m := by
  change ProjectionModels snap (report context leaf [(loSlot,hiSlot)]) m
  rw [report_exact]
  refine ⟨(fun _ h => nomatch h),(fun _ h => nomatch h),?_,?_⟩
  · intro first present
    cases List.mem_singleton.mp present
    intro _ _ _ _ absent; cases absent
  · intro first present
    cases List.mem_singleton.mp present
    intro _ _ _ _ _ absent; cases absent

theorem head (m : Assignment) (valid : ParentHolds m) : HeadModels packet m :=
  ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr ⟨new_snapshot m valid,ordinary m valid⟩,
    projections m⟩

end Yulang.GeneralWhereVersionLeafHead317
