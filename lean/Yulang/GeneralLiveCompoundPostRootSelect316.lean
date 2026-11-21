import Yulang.GeneralLiveCompoundPostRootHead316
import Yulang.GeneralLiveCompoundPostLeafCycles316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 42000000
namespace Yulang.GeneralLiveCompoundPostRootSelect316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry declaration leaf boundary_checked)
open GeneralLiveCompoundChildSite316 (child childSite)
open GeneralLiveCompoundPost316 (raw cur raw_sites_after centers_after)
open GeneralLiveCompoundPostFrames316 (rootPlan root_frame_plan)
open GeneralLiveCompoundLeafInstall316 (after after_model reachable)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundPostRootHead316 (known frame prepared schema head_equations unique)
open GeneralNominalVersionedCycles232 (Cyclic)
open GeneralNominalVersionedDiagnostic232 (boundary)
open GeneralNominalRecursiveInspection (Origin inspectMany inspect Report typeArguments)
open GeneralNominalVersionedCandidates231 (inputs)
open CommonNominalFullCarrier

theorem no_semantic : ¬ Cyclic after (.source 0) :=
  GeneralRebaseTreeAcyclic272.acyclic _ _ after_model _ _
    GeneralVersionedEndpointObstructionSelect315.canonical GeneralVersionedEndpointObstructionSelect315.model_origin

theorem no_raw_zero : ¬ GeneralNominalCycleK2.RecursAt raw (0 : Fin 8) := by
  intro bad
  obtain ⟨next,edge,tail⟩ := GeneralNominalCycleK2.recurs_cycle _ _ bad
  have old := GeneralVersionedEndpointObstructionHead315.valid.1.1
  apply GeneralVersionedEndpointObstructionSelect315.no_raw_zero
  refine Or.inr ⟨⟨next,GeneralLiveCompoundPostLeafCycles316.old_edge edge,?_⟩,w,old⟩
  exact GeneralLiveCompoundPostLeafCycles316.map_path (first := raw)
    (last := GeneralMixedCompoundUpperSnapshot307.snap) (fun i => i)
    (fun a b e => GeneralLiveCompoundPostLeafCycles316.old_edge (a := a) (b := b) e) tail

theorem current_tests :
    (GeneralNominalCenteredSteps.inspection rootPlan).tests = [(.source 0,.nominal 0 2)] := by
  let p := GeneralLiveCompoundCurrentRoot316.plan
  let a := GeneralLiveCompoundLeafHead316.packet
  open GeneralNominalVersionedInstallation231 (reserved atoms allocated) in
  change (inspectMany (GeneralDictionaryOrdinaryTransport.extendState p.packet.context.state
    (reserved a) (atoms a) (allocated a))
    (GeneralNominalInspection.queries p.packet.context.state p.packet.context.interpretation p.packet.declaration)
    p.packet.bounds (fun index => p.input.observed.inputs[index]?.join) 0).tests = _
  rw [GeneralDictionaryOrdinaryTransport.inspectMany_extended]
  have prior :
      (GeneralNominalCenteredSteps.inspection p).tests = [(.source 0,.nominal 0 2)] := by
    have args : GeneralNominalRecursiveInspection.typeArguments GeneralLiveCompoundUpperSnapshot316.desc.arguments =
        some [((2 : Fin 8),2),(2,2)] := rfl
    have tag : GeneralLiveCompoundUpperSnapshot316.desc.declaration.name = 0 := rfl
    have obs : (GeneralNominalCenters.rootSite 4 root).observed.inputs[0]?.join =
        some (.source 0) := rfl
    have sub (origins : Nat → Option Origin) :
        (GeneralNominalRecursiveInspection.inspectMany GeneralLiveCompoundUpperSnapshot316.snap
          [.variables [0],.variables [0]] [(2,2),(2,2)] origins 0).tests = [] := by
      simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
        GeneralNominalRecursiveInspection.Report.append]
    change (inspectMany GeneralLiveCompoundUpperSnapshot316.snap
      (GeneralNominalInspection.queries GeneralLiveCompoundUpperSnapshot316.snap
        GeneralLiveCompoundUpperSnapshot316.context.interpretation declaration)
      [((0 : Fin 8),0)] (fun index => (GeneralNominalCenters.rootSite 4 root).observed.inputs[index]?.join) 0).tests = _
    rw [GeneralLiveCompoundCurrentRoot316.query]
    simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
      GeneralNominalRecursiveInspection.Report.append,GeneralNominalRecursiveInspection.Report.visit,args,tag,obs,sub]
  exact prior

abbrev slot0 : Fin 8 := 0
theorem located_zero : GeneralNominalRecursiveCandidates.arguments cur (inputs root) =
    some [(slot0,slot0)] := GeneralLiveCompoundCurrentRoot316.located

theorem safe : B4TargetV8.SafeKnown (boundary roles) registry after root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (bad | (⟨i,cycle⟩ | ⟨site,present,atRoot,i,cycle⟩))
    · obtain ⟨_,_,i,slot,atSource,cycle⟩ := bad
      have rawIndex : slot = (0 : Fin 8) := GeneralMixedCompoundUpperBase307.injective atSource
      subst slot
      exact no_raw_zero cycle
    · exact no_semantic cycle
    · rw [centers_after] at present
      rcases List.mem_cons.mp present with rfl|rest
      · exact no_semantic cycle
      · cases List.mem_singleton.mp rest
        exact GeneralLiveCompoundCurrentRoot316.not_root atRoot
  · rintro (bad | ⟨p,framed,entry,member,cycle⟩)
    · obtain ⟨_,d,visible,_,atRole,_,bounds,found,visited,hit,cycle⟩ := bad
      rcases List.mem_cons.mp visible with first | rest
      · subst d
        have equal : bounds = [((0 : Fin 8),(0 : Fin 8))] := Option.some.inj (found.symm.trans located_zero)
        subst bounds
        change visited ∈ (GeneralNominalRecursiveCandidates.report cur declaration [(slot0,slot0)]).inspected at hit
        have report : (GeneralNominalRecursiveCandidates.report cur declaration [(slot0,slot0)]).inspected = [(slot0,slot0)] := by
          let p := GeneralLiveCompoundCurrentRoot316.plan
          let a := GeneralLiveCompoundLeafHead316.packet
          open GeneralNominalVersionedInstallation231 (reserved atoms allocated) in
          change (GeneralNominalRecursiveCandidates.report
            (GeneralDictionaryOrdinaryTransport.extend p.packet.context (reserved a) (atoms a) (allocated a))
            declaration [(slot0,slot0)]).inspected = _
          rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended]
          exact congrArg GeneralNominalRecursiveInspection.Report.inspected GeneralLiveCompoundCurrentRoot316.report_exact
        rw [report] at hit
        cases List.mem_singleton.mp hit
        exact no_raw_zero cycle
      · cases List.mem_singleton.mp rest; cases atRole
    · have equal := root_frame_plan framed
      subst p
      rw [current_tests] at member
      cases List.mem_singleton.mp member
      exact no_semantic cycle
  · rintro (⟨_,d,visible,atRole,_,bad⟩ | pending)
    · rcases List.mem_cons.mp visible with first | rest
      · subst d; exact bad prepared
      · cases List.mem_singleton.mp rest; cases atRole
    · exact pending (GeneralLiveCompoundAdmin316.admin centers_after (Or.inl rfl))

theorem classes : GeneralNominalVersionedEffects231.ClassEffects after.core root rootPlan w := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  refine ⟨?_,GeneralLiveCompoundAdmin316.equal_outputs raw_sites_after⟩
  intro output member body found
  cases GeneralLiveCompoundAdmin316.all_requests raw_sites_after member
  have same : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
  subst body
  intro equation present
  cases List.mem_singleton.mp present
  change Equivalent (w 4).1 GeneralDictionaryOptionalOutput229.value
  rw [GeneralDictionaryCompoundPrepared238.values.output]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry after root
    (.selected declaration.id [child]) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  refine .ordinary ?_ (.ordinary ?_ (.selected safe unique ?_))
  · rintro ⟨key,kids,picked,_,blocked⟩
    have same := (unique.2 key kids picked.1).1
    subst key
    exact blocked.2.2 ⟨w,after_model,rootPlan,frame,GeneralNominalVersionedHeadSharing232.schema_holds rootPlan w schema⟩
  · exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict after_model
      (fun focus _ => GeneralLiveCompoundAdmin316.equal_outputs raw_sites_after)
      (GeneralLiveCompoundAdmin316.equal_outputs raw_sites_after)
  · intro conflict
    have ready := GeneralNominalVersionedMixedReady235.ready boundary_checked reachable frame
    exact conflict.2 ⟨w,after_model,⟨⟨_,unique⟩,rootPlan,frame,ready,head_equations,classes⟩⟩

end Yulang.GeneralLiveCompoundPostRootSelect316
