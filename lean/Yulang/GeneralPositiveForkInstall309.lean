import Yulang.GeneralPositiveForkPreinstall309
import Yulang.GeneralNominalVersionedMixedCommon235

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralPositiveForkInstall309
open GeneralPositiveForkSource309
open GeneralPositiveForkPlan309 (plan packet loSite hiSite kids vars ordered_children emitted output_schema)
open GeneralPositiveForkPreinstall309 (frame effect safe positions alternatives)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (model context state state_models)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedInstall232 (InstallationModels install install_models)
open GeneralNominalVersionedMixedKernel234 (Installable Committed Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (rootSite)
open CommonNominalFullCarrier

abbrev after := install initial effect

theorem request_exact (output : GeneralSourceState.Output) (h : output ∈ requests initial.core root) :
    output = ⟨0,1⟩ := by
  obtain ⟨site,present,_,within⟩ := mem_requests_iff.mp h
  cases List.mem_singleton.mp present
  exact List.mem_singleton.mp within

theorem class_effects (m : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects initial.core root plan m := by
  constructor
  · intro output member body found
    cases request_exact output member
    have same : body = .explicit associated := (Option.some.inj found).symm
    subst body
    intro eq inBody
    cases List.mem_singleton.mp inBody
    change Equivalent (m 1).1 (GeneralNominalVersionedPlans231.variables plan m .actual 0)
    rw [vars]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro a x b y _
    cases request_exact a x
    cases request_exact b y
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem installation (m : Assignment) (valid : Models initial m) : InstallationModels initial effect m :=
  (GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ init_reached rfl rfl).mpr
    ⟨valid,GeneralPositiveForkPlan309.holds m valid.1.1,class_effects m⟩

theorem installable : Installable compiled initial effect := by
  refine ⟨rfl,rfl,safe,?_,?_,(by intro _ absent; cases absent),positions,alternatives,model,installation model init_model⟩
  · exact GeneralNominalVersionedMixedObservations233.legacy_cache
      (GeneralDictionaryDefaultCache208.initial_valid (context true) root)
  · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
    rw [output_schema]

theorem novel : ¬ Committed initial plan := by
  intro committed
  have impossible := committed.2 loSite.occurrence (ordered_children ▸ List.mem_cons_self)
  cases impossible

theorem step : Step compiled root initial after := ⟨root,.root,.install effect installable novel⟩

theorem reachable : B4TargetV8.Reachable (boundary roles) registry root after :=
  ⟨initial,actual_initial,.tail .refl step⟩

theorem models (m : Assignment) : Models after m ↔ Models initial m :=
  ⟨GeneralNominalVersionedMixedKernel234.step_models step,
    fun before => (install_models rfl).mpr (installation m before)⟩

theorem inhabited : Models after model := (models _).mpr init_model

theorem edges : after.core.erased.current.edges =
    [(root,loSite.occurrence),(root,hiSite.occurrence)] := by
  change GeneralNominalVersionedChildren232.edges plan = _
  unfold GeneralNominalVersionedChildren232.edges
  rw [ordered_children]
  rfl

theorem actual_low : GeneralNominalSaturationState.Generated after.core.erased.current root loSite.occurrence :=
  .child .root (edges ▸ List.mem_cons_self)

theorem actual_high : GeneralNominalSaturationState.Generated after.core.erased.current root hiSite.occurrence :=
  .child .root (edges ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem centers : after.core.sites = [rootSite (state true).seed root,loSite,hiSite] := by
  change [rootSite (state true).seed root] ++ GeneralNominalVersionedChildren232.emitted plan = _
  rw [emitted]
  rfl

theorem raw_sites : after.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,loSite.observed,hiSite.observed] := by
  change [GeneralNominalDemandMerging.pointSite root] ++ GeneralNominalVersionedChildren232.rawSites plan = _
  unfold GeneralNominalVersionedChildren232.rawSites
  rw [emitted]
  rfl

end Yulang.GeneralPositiveForkInstall309
