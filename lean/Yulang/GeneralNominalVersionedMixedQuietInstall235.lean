import Yulang.GeneralNominalVersionedMixedSelectedEffect235
import Yulang.GeneralNominalVersionedInstallProperties232
set_option backward.isDefEq.respectTransparency false
/-! Installation does not add class-output requests when its ordered versioned
children have no outputs. This includes nonterminal parents; it assumes neither
common models nor parent evidence. No such equality is asserted for arbitrary
output-bearing children. -/
namespace Yulang.GeneralNominalVersionedMixedQuietInstall235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalVersionedChildren232
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

def Quiet (plan : Plan roles) : Prop :=
  ∀ child ∈ GeneralNominalVersionedFrame231.children plan.packet, child.demand.outputs = []

theorem terminal_quiet (terminal : GeneralNominalVersionedFrame231.children plan.packet = []) : Quiet plan := by
  intro child member
  rw [terminal] at member
  cases member

theorem requests_iff (quiet : Quiet plan) :
    output ∈ GeneralNominalCenteredHeadOutputs.requests (installCore core plan) demand ↔
      output ∈ GeneralNominalCenteredHeadOutputs.requests core demand := by
  constructor
  · intro member
    obtain ⟨site,present,alias,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
    change site ∈ core.erased.current.sites ++ rawSites plan at present
    rcases List.mem_append.mp present with present | present
    · exact GeneralNominalCenteredHeadOutputs.mem_requests_iff.mpr
        ⟨site,present,GeneralNominalVersionedInstallProperties232.alias_iff.mp alias,within⟩
    · change site ∈ (emitted plan).map Site.observed at present
      obtain ⟨center,centerPresent,siteEq⟩ := List.mem_map.mp present
      subst site
      have child : center.occurrence ∈ GeneralNominalVersionedFrame231.children plan.packet := by
        rw [← emitted_occurrences plan]
        exact List.mem_map.mpr ⟨center,centerPresent,rfl⟩
      change output ∈ center.occurrence.demand.outputs at within
      rw [quiet _ child] at within
      cases within
  · exact requests_included core plan output

theorem installation_models_iff
    (snapshot : effect.snapshot = state.core) (quiet : Quiet effect.plan) (model) :
    InstallationModels state effect model ↔ Models state model ∧
      GeneralNominalVersionedPlans231.Holds effect.plan model ∧ effect.Holds model := by
  constructor
  · exact fun valid => ⟨valid.1,valid.2.1,valid.2.2.1⟩
  · rintro ⟨valid,packet,chosen⟩
    refine ⟨valid,packet,chosen,?_,?_,?_⟩
    · apply live_restrict (fun _ member => (requests_iff quiet).mp member)
      exact snapshot ▸ chosen.2
    · intro prior member
      apply GeneralNominalCenteredHeadMatEffects.restrict (fun _ present => (requests_iff quiet).mp present)
      exact (valid.1.2.2.2.2.2 prior member).2
    · intro prior member
      apply live_restrict (fun _ present => (requests_iff quiet).mp present)
      exact (valid.2.2 prior member).2

theorem common_iff (snapshot : effect.snapshot = state.core) (quiet : Quiet effect.plan) :
    (∃ model, InstallationModels state effect model) ↔
      ∃ model, Models state model ∧ GeneralNominalVersionedPlans231.Holds effect.plan model ∧
        GeneralNominalVersionedEffects231.ClassEffects state.core effect.plan.packet.site.occurrence effect.plan model := by
  constructor
  · rintro ⟨model,valid⟩
    exact ⟨model,valid.1,valid.2.1,snapshot ▸ valid.2.2.1.2⟩
  · rintro ⟨model,valid,packet,classes⟩
    exact ⟨model,(installation_models_iff snapshot quiet model).mpr
      ⟨valid,packet,GeneralNominalVersionedPlans231.head_models packet,snapshot.symm ▸ classes⟩⟩

theorem source_installable_iff
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence (.selected key children))
    (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry)
    (snapshot : effect.snapshot = state.core) (quiet : Quiet effect.plan) :
    GeneralNominalVersionedMixedKernel234.Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect ↔
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
      ∃ model, Models state model ∧ GeneralNominalVersionedPlans231.Holds effect.plan model ∧
        GeneralNominalVersionedEffects231.ClassEffects state.core effect.plan.packet.site.occurrence effect.plan model := by
  rw [GeneralNominalVersionedMixedSelectedEffect235.source_installable_iff path selected registryEq snapshot]
  exact and_congr Iff.rfl (common_iff snapshot quiet)

end Yulang.GeneralNominalVersionedMixedQuietInstall235
