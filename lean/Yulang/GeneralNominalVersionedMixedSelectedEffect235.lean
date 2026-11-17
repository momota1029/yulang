import Yulang.GeneralNominalVersionedMixedSelectedFrame235
import Yulang.GeneralNominalVersionedMixedGuardReduction235
import Yulang.GeneralNominalVersionedMixedReady235
set_option backward.isDefEq.respectTransparency false
/-! Source reachability and selection provide an actual current effect, Ready,
materialization, all cycle guards and cache. Only choice and common installation
semantics remain in the exact installability characterization. -/
namespace Yulang.GeneralNominalVersionedMixedSelectedEffect235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedMixedFrameSelection235
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

theorem source_effect
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children)) :
    ∃ effect : Effect roles, effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry ∧
      effect.snapshot = state.core ∧ effect.plan.packet.site.occurrence = demand ∧
      effect.plan.packet.declaration.id = key ∧ GeneralNominalVersionedFrame231.children effect.plan.packet = children := by
  obtain ⟨plan,frame,kids⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
  let ready := GeneralNominalVersionedMixedReady235.ready checked path frame
  let effect := effect_of_selected (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected) frame ready
  exact ⟨effect,rfl,rfl,frame.occurrence_eq,frame.key_eq,kids⟩

def Extension (state : State roles) (effect : Effect roles) : Prop :=
  GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
    ∃ model, GeneralNominalVersionedInstall232.InstallationModels state effect model

theorem source_installable_iff
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence (.selected key children))
    (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry)
    (snapshot : effect.snapshot = state.core) :
    Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect ↔ Extension state effect := by
  have frame := effect.frame
  rw [registryEq,snapshot] at frame
  rw [GeneralNominalVersionedMixedGuardReduction235.installable_iff registryEq snapshot
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)
    (GeneralNominalVersionedMixedEmbedding234.source_cache path)]
  exact and_iff_right (GeneralNominalVersionedMixedReady235.materialized path frame)

end Yulang.GeneralNominalVersionedMixedSelectedEffect235
