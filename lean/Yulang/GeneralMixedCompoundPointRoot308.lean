import Yulang.GeneralMixedCompoundPointSites308
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralMixedCompoundPointRoot308
open GeneralDictionaryJournalRefinement228Source (snapshot roles root interpretation)
open GeneralDictionaryCompoundSource238
open GeneralMixedCompoundPointView308 (snap context)
open GeneralMixedCompoundPointViewTrust308 (observed)
open GeneralDictionaryCompoundSites238 (root_raw root_center)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩

theorem query : GeneralNominalInspection.queries snap interpretation declaration =
    [.nominal 0 [.variables [0],.variables [0]]] := GeneralMixedCompoundPointChild308.query

theorem report_exact : report context declaration [(0,0)] =
    { inspected := [(0,0)], checked := [(0,0),(0,0),(2,2),(2,2)],
      captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
      anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
  have sub : inspectMany snap [.variables [0],.variables [0]] [(2,2),(2,2)]
      (fun index => some (.nominal (.source 0) 0 index)) 0 =
      { captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
        checked := [(2,2),(2,2)],
        anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
    simp [inspectMany,inspect,Report.append]
  unfold report
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem bindings_exact : packet.bindings = [(0,2,2),(0,2,2)] := by
  change bindings snap (report context declaration [(0,0)]) = _
  rw [report_exact]
  rfl
theorem located : arguments context (GeneralNominalVersionedCandidates231.inputs root) = some [(0,0)] := by
  decide +kernel

theorem frame_plan {candidate : Plan roles}
    (framed : GeneralNominalVersionedEvidence231.Frame registry observed.core root key candidate) :
    candidate = plan := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = context := framed.context_eq
  have declEq : decl = declaration := List.mem_singleton.mp framed.visible
  have siteEq : site = GeneralNominalDemandMerging.pointSite root := by
    have seen := framed.raw_recorded
    rw [GeneralMixedCompoundPointSites308.raw_sites] at seen
    rcases List.mem_cons.mp seen with same | after
    · exact same
    · cases List.mem_singleton.mp after
      exact False.elim (GeneralDictionaryCompoundSites238.child_not_root framed.occurrence_eq)
  have inputSame : input = rootSite snapshot.seed root := by
    have seen := framed.center_recorded
    rw [GeneralMixedCompoundPointSites308.centers] at seen
    rcases List.mem_cons.mp seen with same | after
    · exact same
    · cases List.mem_singleton.mp after
      exact False.elim (GeneralDictionaryCompoundSites238.child_not_root (inputEq.trans framed.occurrence_eq))
  subst reg; subst ctx; subst decl; subst site; subst input
  have boundsEq : [(0,0)] = bounds := Option.some.inj (located.symm.trans framed.located)
  subst bounds
  rfl


open GeneralMixedCompoundPointFirstPlan308 (candidateModel)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (Holds head_models)
open GeneralNominalVersionedCandidates231 (Prepared Survivor Unique)
open GeneralNominalCenteredHeadMatPlanData (Same)

theorem same_readback : Same GeneralMixedCompoundPointFirstPlan308.plan plan := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  change GeneralNominalReportErasure.erase _ (report _ declaration [(0,0)]) =
    GeneralNominalReportErasure.erase _ (report context declaration [(0,0)])
  rw [GeneralDictionaryCompoundCurrent238.report_exact,report_exact]
  rfl

theorem models_observed : Models observed candidateModel :=
  (GeneralMixedCompoundPointViewTrust308.models _).mpr GeneralMixedCompoundPointFirstInstall308.point_first_held

theorem held (m : GeneralNominalCommonBridge.Assignment) (h : Models observed m) : Holds plan m :=
  GeneralDeferredLadderTransport302.held_of_reindex same_readback m
    (GeneralMixedCompoundPointFirstPublic308.installed_held m ((GeneralMixedCompoundPointViewTrust308.models _).mp h)) h.1.1

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snap registry root.identity packet.bindings := by
  intro key member _
  have same := GeneralNominalCenteredHeadMatPlanData.bindings same_readback
  rw [← same] at member
  change key ∈ GeneralNominalVersionedInstallation231.allocated GeneralMixedCompoundPointFirstPlan308.pkt
  exact member

theorem prepared : Prepared registry context root declaration := by
  have term : 0 ∈ GeneralNominalState.sources snap := GeneralNominalAllocationSupport.slot_source snap 0
  have linked : GeneralNominalState.Linked snap (GeneralNominalVersionedCandidates231.inputs root).demand := by
    refine ⟨?_,fun _ absent => nomatch absent⟩
    intro i
    have zero : i = 0 := Fin.ext (by exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (show i.val < 1 from i.isLt)))
    subst i
    exact ⟨term,term⟩
  refine ⟨GeneralDictionaryCompoundSource238.source.metadata,
    linked,
    [(0,0)],located,fresh,?_,candidateModel,head_models (held _ models_observed)⟩
  rw [report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem child_exact :
    GeneralNominalVersionedFrame231.children packet = [GeneralDictionaryCompoundSites238.childSite.occurrence] :=
  (GeneralDeferredLadderTransport302.children_eq same_readback).symm.trans
    GeneralMixedCompoundPointFirstInstall308.actual_children

theorem frame : GeneralNominalVersionedEvidence231.Frame registry observed.core root declaration.id plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,List.mem_singleton_self _,rfl,located,prepared⟩
  · rw [GeneralMixedCompoundPointSites308.raw_sites]; exact List.mem_cons_self
  · rw [GeneralMixedCompoundPointSites308.centers]; exact List.mem_cons_self

end Yulang.GeneralMixedCompoundPointRoot308
