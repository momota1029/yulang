import Yulang.GeneralLiveCompoundPostLeafCycles316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 42000000
namespace Yulang.GeneralLiveCompoundPostLeafSelect316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry leaf declaration checked)
open GeneralLiveCompoundPost316 (raw cur raw_sites_after centers_after aliases_after)
open GeneralLiveCompoundLeafInstall316 (after after_model)
open GeneralLiveCompoundChildSite316 (child childSite ref center_id)
open GeneralLiveCompoundPostFrames316 (leafPlan leaf_frame_plan leaf_frame leaf_held)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundPostLeafCycles316 (no_lo no_mid no_raw)
open GeneralLiveCompoundAdmin316
open GeneralNominalVersionedDiagnostic232 (boundary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters GeneralSourceDictionaries GeneralDeclarations
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedCandidates231 (inputs Survivor Unique)
open GeneralNominalVersionedJournal232 (Models)
open CommonNominalFullCarrier

abbrev lowSlot : Fin 8 := 5
abbrev highSlot : Fin 8 := 6

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry cur child leaf := leaf_frame.prepared

theorem known : ¬ GeneralNominalState.RootPending raw (inputs child).demand :=
  GeneralLiveCompoundLeafEvidence316.known

theorem located : GeneralNominalRecursiveCandidates.arguments cur (inputs child) =
    some [(lowSlot,highSlot)] := GeneralLiveCompoundChildSite316.located

theorem terminal : GeneralNominalVersionedFrame231.children leafPlan.packet = [] := by
  unfold GeneralLiveCompoundPostFrames316.leafPlan GeneralNominalVersionedInstallation231.replayPlan
  rw [GeneralNominalVersionedTransport231.plan_packet,GeneralNominalVersionedTransport231.children_eq,
    GeneralLiveCompoundLeafEvidence316.terminal]

theorem survivor : Survivor registry cur child leaf.id [] :=
  ⟨known,leaf,List.mem_cons_of_mem _ (List.mem_singleton_self _),
    GeneralLiveCompoundRegistry316.leaf_checked,rfl,rfl,[(lowSlot,highSlot)],located,prepared,terminal.symm⟩

theorem unique : Unique registry cur child leaf.id [] := by
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,idEq,role,_,_,_,_⟩ := copy
  rcases List.mem_cons.mp visible with h | h
  · subst d; cases role
  · cases List.mem_singleton.mp h
    subst key
    exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked other survivor⟩

theorem center_child {site} (present : site ∈ after.core.sites)
    (atChild : site.occurrence = child) : site = childSite := by
  rw [centers_after] at present
  rcases List.mem_cons.mp present with rfl | last
  · exact False.elim (GeneralLiveCompoundCurrentRoot316.not_root atChild.symm)
  · exact List.mem_singleton.mp last

theorem inherited :
    (GeneralNominalCenteredSteps.inspection leafPlan).inspected = [(lowSlot,highSlot)] ∧
    (GeneralNominalCenteredSteps.inspection leafPlan).tests = [(ref,.structural (.variant 0))] := by
  let p := GeneralLiveCompoundLeafHead316.plan
  let a := GeneralLiveCompoundLeafHead316.packet
  open GeneralNominalVersionedInstallation231 (reserved atoms allocated) in
  change let result := (inspectMany (GeneralDictionaryOrdinaryTransport.extendState p.packet.context.state
    (reserved a) (atoms a) (allocated a))
    (GeneralNominalInspection.queries p.packet.context.state p.packet.context.interpretation p.packet.declaration)
    p.packet.bounds (fun index => p.input.observed.inputs[index]?.join) 0)
    result.inspected = _ ∧ result.tests = _
  simp only [GeneralDictionaryOrdinaryTransport.inspectMany_extended]
  exact GeneralLiveCompoundLeafSelect316.inherited

theorem report_exact : (GeneralNominalRecursiveCandidates.report cur leaf [(lowSlot,highSlot)]).inspected =
    [(lowSlot,highSlot)] := by
  let a := GeneralLiveCompoundLeafHead316.packet
  open GeneralNominalVersionedInstallation231 (reserved atoms allocated) in
  change (GeneralNominalRecursiveCandidates.report
    (GeneralDictionaryOrdinaryTransport.extend a.context (reserved a) (atoms a) (allocated a))
    leaf [(lowSlot,highSlot)]).inspected = _
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended]
  exact congrArg Report.inspected GeneralLiveCompoundChildSite316.leaf_report

theorem safe_positions : GeneralNominalVersionedCycles232.Safe after leafPlan := by
  rw [GeneralNominalVersionedCycles232.Safe,inherited.1,inherited.2]
  refine ⟨rfl,?_⟩
  intro entry member
  cases List.mem_singleton.mp member
  exact no_mid

theorem safe : B4TargetV8.SafeKnown (boundary roles) registry after child := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (raw | (⟨i,cycle⟩ | ⟨site,present,atChild,i,cycle⟩))
    · obtain ⟨_,_,i,slot,atSource,cycle⟩ := raw
      have indexEq : i = 0 := Fin.ext (by
        have b : i.val < 1 := i.isLt
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ b))
      subst i
      have loc : slot = (5 : Fin 8) := GeneralMixedCompoundUpperBase307.injective atSource
      subst slot
      exact no_raw cycle
    · have indexEq : i = 0 := Fin.ext (by
        have b : i.val < 1 := i.isLt
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ b))
      subst i
      exact no_lo cycle
    · cases center_child present atChild
      have idx : i = 0 := Fin.ext (by
        have b : i.val < 1 := i.isLt
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ b))
      subst i
      exact no_mid (by simpa only [center_id] using cycle)
  · rintro (raw | ⟨p,framed,entry,member,cycle⟩)
    · obtain ⟨_,d,visible,_,role,_,bounds,found,visited,hit,cycle⟩ := raw
      rcases List.mem_cons.mp visible with one | last
      · subst d; cases role
      · cases List.mem_singleton.mp last
        change GeneralNominalRecursiveCandidates.arguments cur (inputs child) = some bounds at found
        have eq := Option.some.inj (located.symm.trans found)
        subst bounds
        change visited ∈ (GeneralNominalRecursiveCandidates.report cur leaf [(lowSlot,highSlot)]).inspected at hit
        rw [report_exact] at hit
        cases List.mem_singleton.mp hit
        exact no_raw cycle
    · have eq := leaf_frame_plan framed
      subst p
      exact safe_positions.2 entry member cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | pending)
    · rcases List.mem_cons.mp visible with one | last
      · subst d; cases role
      · cases List.mem_singleton.mp last
        exact unprepared prepared
    · exact pending (admin centers_after (Or.inr rfl))

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry after child (.selected leaf.id []) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  have holds := leaf_held after_model
  have head := GeneralNominalVersionedDiagnostic232.head_equations holds
  refine .ordinary ?_ (.ordinary ?_ (.selected safe unique ?_))
  · rintro ⟨key,kids,picked,_,blocked⟩
    have same := (unique.2 key kids picked.1).1
    subst key
    exact blocked.2.2 ⟨w,after_model,leafPlan,leaf_frame,
      GeneralNominalVersionedHeadSharing232.schema_holds leafPlan w head.2.2⟩
  · exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict after_model
      (fun focus _ => equal_outputs raw_sites_after) (equal_outputs raw_sites_after)
  · intro conflict
    have ready : GeneralNominalCenteredHeadMatEffects.Ready after.core child leafPlan :=
      fun output h => False.elim (leaf_requests raw_sites_after aliases_after output h)
    exact conflict.2 ⟨w,after_model,⟨⟨_,unique⟩,leafPlan,leaf_frame,ready,head,
      leaf_classes raw_sites_after aliases_after leafPlan⟩⟩

end Yulang.GeneralLiveCompoundPostLeafSelect316
