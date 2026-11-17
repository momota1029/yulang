import Yulang.GeneralNominalVersionedMixedStableEvidence235
import Yulang.GeneralNominalVersionedMixedEmbedding234
set_option backward.isDefEq.respectTransparency false
/-! The remaining current-candidate obligations, independent of the desired
Evidence/Committed conclusion. Selection supplies safety, Reachable supplies
current cache; the other guarded-install obligations remain explicit. -/
namespace Yulang.GeneralNominalVersionedMixedCurrentCandidate235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

structure Current (registry : Registry) (state : State roles) (demand : Occurrence roles) (effect : Effect roles) : Prop where
  registry_eq : effect.registry = registry
  snapshot_eq : effect.snapshot = state.core
  occurrence_eq : effect.plan.packet.site.occurrence = demand
  materialized : (GeneralNominalVersionedPlans231.emittedSchema effect.plan).unknown = false
  choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet
  positions : GeneralNominalVersionedCycles232.Safe state effect.plan
  alternatives : AlternativesSafe registry state effect.plan.input
  common : ∃ model, GeneralNominalVersionedInstall232.InstallationModels state effect model

theorem selected_safe
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state demand (.selected key children)) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry state demand := by
  have chosen := (B4TargetV7.selected_iff.mp (B4TargetV8.selected_iff.mp
    (GeneralNominalVersionedMixedBoundary234.local_iff.mp selected)).1).1
  cases chosen with
  | selected safe _ _ => exact safe

theorem installable (current : Current registry state demand effect)
    (cache : GeneralNominalVersionedMixedKernelCache234.Valid state)
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state demand (.selected key children)) :
    Installable registry state effect :=
  ⟨current.registry_eq,current.snapshot_eq,current.occurrence_eq.symm ▸ selected_safe selected,
    cache,current.materialized,current.choice,current.positions,current.alternatives,current.common⟩

theorem source_installable
    (current : Current (GeneralNominalCenteredHeadAllocEncoding.registry registry) state demand effect)
    (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children)) :
    Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect :=
  installable current (GeneralNominalVersionedMixedEmbedding234.source_cache reachable)
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)

end Yulang.GeneralNominalVersionedMixedCurrentCandidate235
