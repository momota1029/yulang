import Yulang.GeneralGeneratedDisplayTable299
import Yulang.GeneralRebaseCompiledRetag277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 9800000
namespace Yulang.GeneralGeneratedDisplayParentCurrent299
open GeneralNominalExamples (registry model displayRoot displayChild state)
open GeneralDeclarationExamples (roles)
open GeneralNominalNonleafPlan193 (centerSite)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models State Effect)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseDisplayFrame276 (classes_empty)
open GeneralRebaseCompiledDisplay277 (after compiled effect)
open GeneralRebaseCompiledSelection277 (parent parent_frame unique_parent after_model picked_parent)
open GeneralNominalVersionedMixedCurrentCandidate235 (Current source_installable)
open GeneralNominalVersionedInstall232 (InstallationModels installCore)
open GeneralNominalVersionedChildren232 (emitted rawSites)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralNominalCenteredHeadOutputs (requests)

noncomputable def certificate : Effect roles :=
  ⟨compiled,after.core,parent,parent_frame,
    GeneralRebaseCompiledSelection277.parent_children.symm ▸ unique_parent,
    GeneralRebaseCompiledEvidence277.ready parent⟩

theorem original_sites : emitted GeneralRebaseCompiledDisplay277.parent = [centerSite] := by
  have length : (emitted GeneralRebaseCompiledDisplay277.parent).length = 1 :=
    GeneralNominalVersionedChildren232.emitted_length _
  have member : centerSite ∈ emitted GeneralRebaseCompiledDisplay277.parent := by
    unfold emitted
    have seen : GeneralDeclarationExamples.displayChild ∈
        GeneralCanonicalChildOrder.canonicalRequirements
          GeneralRebaseCompiledDisplay277.parent.packet.declaration.requirements :=
      (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mp (List.mem_singleton_self _)
    refine List.mem_map.mpr ⟨⟨_,seen⟩,List.mem_attach _ _,?_⟩
    exact (GeneralRebaseCompiledRetag277.childSite_eq GeneralNominalNonleafPlan193.plan compiled rfl
      GeneralDeclarationExamples.displayChild _).trans GeneralRebaseDisplayPacket276.child_site
  obtain ⟨site,eq⟩ := List.length_eq_one_iff.mp length
  rw [eq] at member ⊢
  cases List.mem_singleton.mp member
  rfl

theorem replay_sites : emitted parent = [centerSite] := by
  rw [← original_sites]
  unfold emitted
  apply List.map_congr_left
  intro clause _
  exact GeneralNominalVersionedTransport231.childSite_eq _ _ _ _ clause.val _

theorem new_raw_site (site) (seen : site ∈ (installCore after.core parent).erased.current.sites) :
    site ∈ after.core.erased.current.sites := by
  change site ∈ after.core.erased.current.sites ++ rawSites parent at seen
  rcases List.mem_append.mp seen with old|new
  · exact old
  · rw [rawSites,replay_sites] at new
    cases List.mem_singleton.mp new
    rw [GeneralRebaseCompiledEvidence277.raw_sites]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem no_additional_requests (focus) (out) :
    out ∈ requests (installCore after.core parent) focus ↔ out ∈ requests after.core focus := by
  constructor
  · intro hit
    exact GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases (root := focus) new_raw_site (fun _ h => h) hit
  · exact GeneralNominalVersionedInstall232.requests_included (root := focus) after.core parent out

theorem noRequests (focus) : requests (installCore after.core parent) focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  have before := (no_additional_requests focus output).mp member
  rw [GeneralRebaseCompiledInstall277.no_new_request] at before
  cases before

theorem commonModel : InstallationModels after certificate model := by
  have held := GeneralNominalVersionedInstalledEvidence233.replay_holds after_model
  refine ⟨after_model,held,⟨GeneralNominalVersionedPlans231.head_models held,
    classes_empty (GeneralRebaseCompiledInstall277.no_new_request displayRoot) parent model⟩,
    classes_empty (noRequests displayRoot) parent model,?_,?_⟩
  · intro old member
    cases member
  · intro old member
    exact classes_empty (noRequests old.plan.packet.site.occurrence) old.plan model

theorem compatible : GeneralNominalCycleSteps.ChoiceCompatible after.core.erased.current parent.packet := by
  intro old member _
  change old ∈ [GeneralRebaseCompiledDisplay277.parent.packet] at member
  cases List.mem_singleton.mp member
  rfl

theorem inspection_length :
    (GeneralNominalCenteredSteps.inspection parent).inspected.length =
      (GeneralNominalCenteredSteps.inspection parent).tests.length := by
  decide +kernel

theorem positions : GeneralNominalVersionedCycles232.Safe after parent :=
  ⟨inspection_length, fun entry _ => GeneralRebaseDisplaySafety276.semantic after_model entry.1⟩

theorem alternatives : GeneralNominalVersionedMixedKernel234.AlternativesSafe compiled after parent.input := by
  intro plan _ frame
  have eq := GeneralRebaseCompiledStable277.framed_parent frame
  subst plan
  exact positions

theorem current : Current compiled after displayRoot certificate := by
  refine ⟨rfl,rfl,rfl,?_,compatible,positions,alternatives,⟨model,commonModel⟩⟩
  change (GeneralNominalVersionedPlans231.emittedSchema parent).unknown = false
  rw [show GeneralNominalVersionedPlans231.emittedSchema parent =
      GeneralNominalVersionedPlans231.emittedSchema GeneralRebaseCompiledDisplay277.parent from
    GeneralNominalVersionedTransport231.emittedSchema_eq _ _ _ _,
    GeneralRebaseCompiledRetag277.schema_eq]
  exact congrArg (fun x => x.unknown) GeneralRebaseDisplayPacket276.emitted

theorem installable_but_committed :
    GeneralNominalVersionedMixedKernel234.Installable compiled after certificate ∧
      GeneralNominalVersionedMixedKernel234.Committed after certificate.plan :=
  ⟨source_installable current GeneralRebaseCompiledInstall277.reachable picked_parent,
    GeneralRebaseCompiledStable277.committed_parent⟩

end Yulang.GeneralGeneratedDisplayParentCurrent299
