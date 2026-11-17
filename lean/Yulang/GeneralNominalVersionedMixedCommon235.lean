import Yulang.GeneralNominalVersionedMixedCompletionRequests235
import Yulang.GeneralNominalVersionedMixedHistory235
import Yulang.GeneralNominalVersionedMixedRegistry234
import Yulang.GeneralNominalVersionedMixedSelectedEffect235
set_option backward.isDefEq.respectTransparency false
/-! For actual source-reachable current effects, future live equations impose
no extra installation obligation: canonical child output request identities
already agree on every existing class. A common current model is still needed;
independent existential witnesses are not combined without proof. -/
namespace Yulang.GeneralNominalVersionedMixedCommon235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalCenteredHeadMatCompletionRequests (Present)
open GeneralNominalCenteredHeadOutputs (requests)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {state : State roles} {effect : Effect roles}

theorem requests_iff
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry)
    (snapshot : effect.snapshot = state.core) (present : Present state.core focus.identity) :
    output ∈ requests (installCore state.core effect.plan) focus ↔ output ∈ requests state.core focus :=
  GeneralNominalVersionedMixedCompletionRequests235.install_requests
    (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2
    (GeneralNominalVersionedMixedCompletionRequests235.reachable path)
    (registryEq ▸ snapshot ▸ effect.frame) present output

theorem installation_models_iff
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry)
    (snapshot : effect.snapshot = state.core) :
    InstallationModels state effect model ↔
      Models state model ∧ GeneralNominalVersionedPlans231.Holds effect.plan model ∧ effect.Live state.core model := by
  have frame := snapshot ▸ effect.frame
  have present : Present state.core effect.plan.packet.site.occurrence.identity :=
    ⟨effect.plan.packet.site,frame.raw_recorded,rfl⟩
  constructor
  · rintro ⟨valid,held,chosen,_⟩
    exact ⟨valid,held,snapshot ▸ chosen.2⟩
  · rintro ⟨valid,held,live⟩
    refine ⟨valid,held,⟨GeneralNominalVersionedPlans231.head_models held,snapshot.symm ▸ live⟩,?_,?_,?_⟩
    · exact live_restrict (fun _ member => (requests_iff checked path registryEq snapshot present).mp member) live
    · intro prior member
      rw [(GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty path).2] at member
      cases member
    · intro prior member
      have generated := GeneralNominalVersionedMixedHistory235.parent_generated path member
      obtain ⟨raw,present,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
        (GeneralNominalVersionedMixedTrace235.reachable path).1 generated
      have registered : Present state.core prior.plan.packet.site.occurrence.identity :=
        ⟨raw,present,congrArg Occurrence.identity same⟩
      exact live_restrict (fun _ present => (requests_iff checked path registryEq snapshot registered).mp present)
        (valid.2.2 prior member).2

theorem source_installable_iff
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence
      (.selected key children))
    (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry)
    (snapshot : effect.snapshot = state.core) :
    GeneralNominalVersionedMixedKernel234.Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect ↔
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
      ∃ model, Models state model ∧ GeneralNominalVersionedPlans231.Holds effect.plan model ∧ effect.Live state.core model := by
  rw [GeneralNominalVersionedMixedSelectedEffect235.source_installable_iff path selected registryEq snapshot]
  constructor
  · rintro ⟨choice,model,valid⟩
    exact ⟨choice,model,(installation_models_iff checked path registryEq snapshot).mp valid⟩
  · rintro ⟨choice,model,valid⟩
    exact ⟨choice,model,(installation_models_iff checked path registryEq snapshot).mpr valid⟩

end Yulang.GeneralNominalVersionedMixedCommon235
