import Yulang.GeneralLiveCompoundLeafCycles316
import Yulang.GeneralLiveCompoundAdmin316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 28000000
namespace Yulang.GeneralLiveCompoundLeafSelect316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry leaf declaration)
open GeneralLiveCompoundUpperSnapshot316 (snap context)
open GeneralLiveCompoundUpperRefresh316 (upperState cert upper_reachable)
open GeneralLiveCompoundChildSite316
open GeneralLiveCompoundLeafHead316 (packet plan)
open GeneralLiveCompoundLeafEvidence316 (prepared frame unique holds known emitted)
open GeneralLiveCompoundLeafProof316 (valid w schema)
open GeneralLiveCompoundLeafCycles316 (no_lo no_mid no_raw_five)
open GeneralLiveCompoundAdmin316
open GeneralNominalVersionedDiagnostic232 (boundary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters GeneralSourceDictionaries GeneralDeclarations
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalVersionedJournal232 (Models)
open CommonNominalFullCarrier

theorem leaf_declaration {candidate : Plan roles} {key : Nat}
    (h : Frame registry upperState.core child key candidate) : candidate.packet.declaration = leaf := by
  rcases List.mem_cons.mp h.visible with one | last
  · have role := h.role_eq
    rw [one] at role
    cases role
  · exact List.mem_singleton.mp last

theorem raw_child {site} (present : site ∈ upperState.core.erased.current.sites)
    (atChild : site.occurrence = child) : site = childSite.observed := by
  rw [raw_sites] at present
  rcases List.mem_cons.mp present with rfl | last
  · exact False.elim (GeneralLiveCompoundCurrentRoot316.not_root atChild.symm)
  · exact List.mem_singleton.mp last

theorem center_child {site} (present : site ∈ upperState.core.sites)
    (atChild : site.occurrence = child) : site = childSite := by
  rw [centers] at present
  rcases List.mem_cons.mp present with rfl | last
  · exact False.elim (GeneralLiveCompoundCurrentRoot316.not_root atChild.symm)
  · exact List.mem_singleton.mp last

theorem frame_plan {candidate : Plan roles} {key : Nat}
    (h : Frame registry upperState.core child key candidate) : candidate = plan := by
  have decl := leaf_declaration h
  rcases candidate with ⟨⟨reg,ctx,site,d,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := h.registry_eq
  have ctxEq : ctx = context := h.context_eq
  have declEq : d = leaf := decl
  have siteEq : site = childSite.observed := raw_child h.raw_recorded h.occurrence_eq
  have inputSame : input = childSite := center_child h.center_recorded (inputEq.trans h.occurrence_eq)
  subst reg; subst ctx; subst d; subst site; subst input
  have eq := Option.some.inj (located.symm.trans h.located)
  change [(5,6)] = bounds at eq
  subst bounds
  rfl

theorem inherited :
    (GeneralNominalCenteredSteps.inspection plan).inspected = [(5,6)] ∧
    (GeneralNominalCenteredSteps.inspection plan).tests = [(ref,.structural (.variant 0))] := by
  unfold GeneralNominalCenteredSteps.inspection
  rw [leaf_query]
  have sub (o : Nat → Option Origin) :
      (inspectMany snap [.variables [0]] [(4,2)] o 0).tests = [] ∧
      (inspectMany snap [.variables [0]] [(4,2)] o 0).inspected = [] := by
    rw [inspectMany.eq_2,inspectMany.eq_1]
    simp only [inspect.eq_1,Report.append]
    exact ⟨rfl,rfl⟩
  simp [inspectMany,inspect,Report.append,Report.visit,GeneralMixedCompoundUpperBase307.viewHeads,
    raw_input,ref,sub]

theorem safe_positions : GeneralNominalVersionedCycles232.Safe upperState plan := by
  rw [GeneralNominalVersionedCycles232.Safe,inherited.1,inherited.2]
  refine ⟨rfl,?_⟩
  intro entry member
  cases List.mem_singleton.mp member
  exact no_mid

theorem safe : B4TargetV8.SafeKnown (boundary roles) registry upperState child := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (raw | (⟨i,cycle⟩ | ⟨site,present,atChild,i,cycle⟩))
    · obtain ⟨_,_,i,slot,atSource,cycle⟩ := raw
      have indexEq : i = 0 := Fin.ext (by
        have b : i.val < 1 := i.isLt
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ b))
      subst i
      have loc : slot = (5 : Fin 8) := GeneralMixedCompoundUpperBase307.injective atSource
      subst slot
      exact no_raw_five cycle
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
        change GeneralNominalRecursiveCandidates.arguments context (inputs child) = some bounds at found
        have eq := Option.some.inj (located.symm.trans found)
        subst bounds
        change visited ∈ (GeneralNominalRecursiveCandidates.report context leaf [(5,6)]).inspected at hit
        rw [leaf_report] at hit
        cases List.mem_singleton.mp hit
        exact no_raw_five cycle
    · have eq := frame_plan framed
      subst p
      exact safe_positions.2 entry member cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | pending)
    · rcases List.mem_cons.mp visible with one | last
      · subst d; cases role
      · cases List.mem_singleton.mp last
        exact unprepared prepared
    · exact pending (admin centers (Or.inr rfl))

theorem class_effects :
    GeneralNominalVersionedEffects231.ClassEffects upperState.core child plan w :=
  leaf_classes raw_sites rfl plan

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready upperState.core child plan :=
  fun output h => False.elim (leaf_requests raw_sites rfl output h)

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry upperState child (.selected leaf.id []) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  refine .ordinary ?_ (.ordinary ?_ (.selected safe unique ?_))
  · rintro ⟨key,kids,picked,_,blocked⟩
    have same := (unique.2 key kids picked.1).1
    subst key
    exact blocked.2.2 ⟨w,valid,plan,frame,GeneralNominalVersionedHeadSharing232.schema_holds plan w schema⟩
  · exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict valid
      (fun focus _ => equal_outputs raw_sites) (equal_outputs raw_sites)
  · intro conflict
    exact conflict.2 ⟨w,valid,⟨⟨_,unique⟩,plan,frame,ready,
      GeneralNominalVersionedDiagnostic232.head_equations holds,class_effects⟩⟩

end Yulang.GeneralLiveCompoundLeafSelect316
