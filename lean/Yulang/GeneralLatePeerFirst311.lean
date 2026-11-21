import Yulang.GeneralLatePeerGuard311

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralLatePeerFirst311
open GeneralLatePeerSource311
open GeneralLatePeerRoot311
open GeneralLatePeerGuard311 (Known)
open GeneralGeneratedNestedSource299 (model snapshot context snapshot_model listDescriptor)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralNominalVersionedInstall232 (install install_models InstallationModels)
open GeneralNominalVersionedMixedKernel234 (Step Committed)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)
open GeneralSourceDictionaries (Occurrence)

theorem located : arguments context (inputs root) = some [(0,0),(1,1)] := by decide +kernel

theorem known : Known initial root := by
  rintro ⟨i,unknown⟩
  have split : i.val = 0 ∨ i.val = 1 := by have b := i.isLt; change i.val < 2 at b; omega
  rcases split with eq|eq
  · apply unknown
    exact ⟨(0 : Fin 3),eq.symm,Or.inr ⟨listDescriptor 1,rfl⟩⟩
  · apply unknown
    exact ⟨(1 : Fin 3),eq.symm,Or.inr ⟨listDescriptor 2,rfl⟩⟩

theorem fresh (bs : GeneralNominalAllocation.Bindings) :
    GeneralNominalVersionedAllocation231.Fresh snapshot compiled root.identity bs := by
  intro k _ placed
  exact False.elim (Nat.not_lt_of_ge (initial_source.below_seed _ placed)
    (GeneralNominalIdentities.source_above_seed _ _))

theorem prepared : Prepared compiled context root parentCode := by
  refine ⟨⟨rfl,initial_source.metadata.2⟩,
    ⟨initial_source.linked.1,by intro _ empty; cases empty⟩,[(0,0),(1,1)],located,fresh _,?_,model,?_⟩
  · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report packet)
    rw [report]
    exact ⟨rfl,rfl,rfl⟩
  · exact GeneralNominalVersionedPlans231.head_models (holds model snapshot_model)

theorem frame : Frame compiled initial.core root 1 plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_cons_self,rfl,located,prepared⟩

theorem admin : GeneralNominalVersionedDiagnostic232.AdministrativeReady initial root := by
  refine ⟨⟨plan.input,List.mem_singleton_self _,rfl⟩,?_⟩
  intro a first _ b last _
  cases List.mem_singleton.mp first
  cases List.mem_singleton.mp last
  exact .refl _

theorem no_requests (d : Occurrence roles) : GeneralNominalCenteredHeadOutputs.requests initial.core d = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro o present
  obtain ⟨site,member,_,inside⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp present
  cases List.mem_singleton.mp member
  cases inside

theorem classes (m : Assignment) : GeneralNominalVersionedEffects231.ClassEffects initial.core root plan m :=
  GeneralRebaseDisplayFrame276.classes_empty (no_requests root) plan m

theorem pick : Local registry initial root (.selected 1 (GeneralLatePeerGuard311.children plan)) :=
  GeneralLatePeerGuard311.select init_reached frame known rfl initial_model admin (holds model snapshot_model)
    (classes model) (GeneralLatePeerGuard311.no_merged rfl)

abbrev effect := GeneralLatePeerGuard311.effect (p := plan) init_reached frame known
abbrev after := install initial effect

theorem enabled : GeneralNominalVersionedMixedKernel234.Installable compiled initial effect :=
  GeneralLatePeerGuard311.enabled (p := plan) init_reached frame known pick initial_model (holds model snapshot_model) (classes model)

theorem novel : ¬ Committed initial plan := by
  intro old
  have edge := old.2 direct.occurrence (children_exact ▸ List.mem_cons_self)
  cases edge

theorem step : Step compiled root initial after := ⟨root,.root,.install effect enabled novel⟩

theorem reached : B4TargetV8.Reachable (boundary roles) registry root after :=
  ⟨initial,actual_initial,.tail .refl step⟩

theorem models (m : Assignment) : Models after m ↔ Models initial m :=
  ⟨GeneralNominalVersionedMixedKernel234.step_models step,
    fun valid => (install_models rfl).mpr
      ((GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ init_reached rfl rfl).mpr
        ⟨valid,holds m valid.1.1,classes m⟩)⟩

theorem inhabited : Models after model := (models _).mpr initial_model

theorem centers : after.core.sites = [plan.input,direct,branch] := by
  change [plan.input] ++ GeneralNominalVersionedChildren232.emitted plan = _
  rw [emitted]
  rfl

theorem raw : after.core.erased.current.sites = [plan.packet.site,direct.observed,branch.observed] := by
  change [plan.packet.site] ++ GeneralNominalVersionedChildren232.rawSites plan = _
  unfold GeneralNominalVersionedChildren232.rawSites
  rw [emitted]
  rfl

theorem edges : after.core.erased.current.edges = [(root,direct.occurrence),(root,branch.occurrence)] := by
  change GeneralNominalVersionedChildren232.edges plan = _
  unfold GeneralNominalVersionedChildren232.edges
  rw [children_exact]
  rfl

theorem generated_direct : Generated after.core.erased.current root direct.occurrence := .child .root (edges ▸ List.mem_cons_self)
theorem generated_branch : Generated after.core.erased.current root branch.occurrence :=
  .child .root (edges ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _))

end Yulang.GeneralLatePeerFirst311
