import Yulang.GeneralDepthTwoMiddleFrame300
import Yulang.GeneralDepthTwoCenters300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDepthTwoSecondInstall300
open GeneralGeneratedNestedSource299
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoFirstInstall300 (after actual_middle requests)
open GeneralDepthTwoMiddleContext300 (env plan res updates owns same_children after_center_sites after_raw_sites middle_raw_site holds pendingPlan)
open GeneralDepthTwoMiddleFrame300
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalExamples (registry)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedKernel234 (Step Installable AlternativesSafe)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedInstall232 (install InstallationModels)
open GeneralNominalCenters (Site)
open B4Target (Steps)

abbrev final := install after effect
abbrev rootSite := GeneralDepthTwoRootPlan300.plan.input
abbrev middleSite := GeneralDepthTwoRootPlan300.child
abbrev leafSite := GeneralNominalVersionedFrame231.childSite plan GeneralDeclarationExamples.displayChild
  (display_checked.signature.2.2.2 _ (by simp))

theorem root_observed : rootSite.observed.inputs = [some (.source 0)] := rfl

theorem middle_observed : middleSite.observed.inputs = [some (.source 1)] := by
  change List.ofFn (fun i => some (GeneralNominalRecursiveInspection.Origin.source (middleSite.center i))) = _
  simp [GeneralDepthTwoRootPlan300.child_data.2,List.ofFn_succ]

theorem middle_site : middleSite.occurrence = middle := GeneralDepthTwoRootPlan300.child_data.1

theorem administrative : GeneralNominalVersionedDiagnostic232.AdministrativeReady after middle := by
  constructor
  · exact ⟨middleSite,after_center_sites ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _),middle_site⟩
  · intro a first _ b second same
    rw [after_center_sites] at first second
    simp only [List.mem_cons,List.not_mem_nil,or_false] at first second
    rcases first with rfl|rfl <;> rcases second with rfl|rfl
    · exact .refl _
    · exact False.elim (GeneralDepthTwoCenters300.distinct_center after_model root_observed middle_observed
        (by decide) (by decide) (by decide) same)
    · exact False.elim (GeneralDepthTwoCenters300.distinct_center after_model middle_observed root_observed
        (by decide) (by decide) (by decide) same)
    · exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles)
    compiled after middle := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (raw | (⟨i,cyclic⟩ | ⟨site,_,_,i,cyclic⟩))
    · obtain ⟨_,_,_,slot,_,cyclic⟩ := raw
      exact GeneralDepthTwoSafety300.raw_acyclic env.state rfl after_model.1.1 slot cyclic
    · exact GeneralDepthTwoSafety300.semantic after_model _ cyclic
    · exact GeneralDepthTwoSafety300.semantic after_model _ cyclic
  · rintro (raw | ⟨p,_,entry,_,cyclic⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cyclic⟩ := raw
      exact GeneralDepthTwoSafety300.raw_acyclic env.state rfl after_model.1.1 visited.1 cyclic
    · exact GeneralDepthTwoSafety300.semantic after_model _ cyclic
  · rintro (⟨_,d,visible,role,notFailed,notPrepared⟩ | pending)
    · rcases GeneralRebaseCompiledDisplay277.compiled_members visible (role.trans middle_role) with rfl|rfl
      · exact notFailed wrong_failed
      · exact notPrepared prepared
    · exact pending administrative

theorem positions : GeneralNominalVersionedCycles232.Safe after plan :=
  ⟨by decide +kernel,fun entry _ => GeneralDepthTwoSafety300.semantic after_model entry.1⟩

theorem frame_unique {p : GeneralNominalCenters.Plan roles} {key}
    (given : Frame compiled after.core middle key p) : p = plan := by
  apply GeneralRebaseScopedFrame276.same_frame given frame
  · rcases GeneralRebaseCompiledDisplay277.compiled_members given.visible (given.role_eq.trans middle_role) with wrong|right
    · exact False.elim (wrong_not_prepared (wrong ▸ given.prepared))
    · exact right
  ·
    have row := given.raw_recorded
    rw [after_raw_sites] at row
    simp only [List.mem_cons,List.not_mem_nil,or_false] at row
    rcases row with old|here
    · have eq : root = middle := by
        rw [← given.occurrence_eq,old]
        rfl
      exact False.elim (GeneralGeneratedNestedPredictions299.different_occurrences.1
        (congrArg (fun x => x.identity) eq))
    · exact here.trans middle_raw_site.symm
  · have row := given.center_recorded
    rw [after_center_sites] at row
    simp only [List.mem_cons,List.not_mem_nil,or_false] at row
    rcases row with old|here
    · have eq : root = middle := by
        rw [← given.occurrence_eq,← p.input_exact,old]
        rfl
      exact False.elim (GeneralGeneratedNestedPredictions299.different_occurrences.1
        (congrArg (fun x => x.identity) eq))
    · exact here

theorem alternatives : AlternativesSafe compiled after plan.input := by
  intro p _ framed
  have middleFrame : Frame compiled after.core middle p.packet.declaration.id p :=
    middle_site ▸ framed
  rw [frame_unique middleFrame]
  exact positions

theorem emitted_sites : GeneralNominalVersionedChildren232.emitted plan = [leafSite] := by
  have length : (GeneralNominalVersionedChildren232.emitted plan).length = 1 :=
    GeneralNominalVersionedChildren232.emitted_length _
  have seen : leafSite ∈ GeneralNominalVersionedChildren232.emitted plan := by
    unfold GeneralNominalVersionedChildren232.emitted
    have member : GeneralDeclarationExamples.displayChild ∈
        GeneralCanonicalChildOrder.canonicalRequirements plan.packet.declaration.requirements :=
      (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mp (List.mem_singleton_self _)
    exact List.mem_map.mpr ⟨⟨_,member⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨one,view⟩ := List.length_eq_one_iff.mp length
  rw [view] at seen ⊢
  cases List.mem_singleton.mp seen
  rfl

theorem terminal_site : leafSite.occurrence = terminal := by
  have old := GeneralNominalVersionedChildren232.emitted_occurrences plan
  rw [emitted_sites,same_children] at old
  exact List.singleton_inj.mp old

theorem final_requests (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests final.core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,listed,_,part⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  change site ∈ after.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites plan at listed
  rw [after_raw_sites,GeneralNominalVersionedChildren232.rawSites,emitted_sites] at listed
  simp only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with rfl|rfl|rfl
  · cases part
  · have blank : middleSite.observed.occurrence.demand.outputs = [] := by decide +kernel
    rw [blank] at part; cases part
  · have blank : leafSite.observed.occurrence.demand.outputs = [] := by decide +kernel
    rw [blank] at part; cases part

theorem installation (m : Assignment) (valid : Models after m) :
    InstallationModels after effect m := by
  have planHeld := holds m valid
  refine ⟨valid,planHeld,⟨GeneralNominalVersionedPlans231.head_models planHeld,
    GeneralRebaseDisplayFrame276.classes_empty (requests middle) plan m⟩,
    GeneralRebaseDisplayFrame276.classes_empty (final_requests middle) plan m,?_,?_⟩
  · intro _ no; cases no
  · intro old _
    exact GeneralRebaseDisplayFrame276.classes_empty
      (final_requests old.plan.packet.site.occurrence) old.plan m

theorem enabled : Installable compiled after effect := by
  refine ⟨rfl,rfl,safe,?_,?_,?_,positions,alternatives,model,installation model after_model⟩
  · exact GeneralNominalVersionedMixedEmbedding234.source_cache actual_middle.1
  · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
    rw [show GeneralNominalVersionedPlans231.emittedSchema plan =
          GeneralNominalVersionedPlans231.emittedSchema pendingPlan from
      GeneralNominalVersionedTransport231.emittedSchema_eq .., GeneralDepthTwoMiddlePlan300.emitted_schema]
  · intro old once _
    change old ∈ [GeneralGeneratedNestedPredictions299.parentPacket] at once
    cases List.mem_singleton.mp once
    rfl

theorem actual : (boundary roles).Step registry root after final :=
  ⟨middle,actual_middle.2,.install effect enabled
    (GeneralGeneratedNestedInstallInterface299.second_not_committed rfl rfl same_children)⟩

theorem actual_terminal :
    Steps ((boundary roles).Step registry root) initial final ∧
      B4TargetV8.Reachable (boundary roles) registry root final ∧
      GeneralNominalSaturationState.Generated final.core.erased.current root terminal := by
  obtain ⟨path,reached,emitted,_⟩ := GeneralGeneratedNestedInstallInterface299.cascade rfl
    GeneralDepthTwoFirstInstall300.enabled rfl same_children enabled
  exact ⟨path,reached,emitted⟩

theorem models (m : Assignment) : Models final m ↔ Models after m :=
  ⟨fun valid => GeneralNominalVersionedMixedSourceBoundary234.stepModels actual valid,
    fun valid => (GeneralNominalVersionedInstall232.install_models (effect := effect) rfl).mpr (installation m valid)⟩

end Yulang.GeneralDepthTwoSecondInstall300
