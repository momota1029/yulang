import Yulang.GeneralNominalVersionedChildClosure237
import Yulang.GeneralNominalVersionedMixedCommon235
set_option backward.isDefEq.respectTransparency false
/-! Exact remaining installation obligations at the real source boundary.
The single common-model witness is retained, never replaced by separate ones. -/
namespace Yulang.GeneralNominalVersionedMixedMaterialization237
open GeneralNominalVersionedJournal232 GeneralNominalVersionedPlans231
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

def Residual (state : State roles) (effect : Effect roles) (model : GeneralNominalCommonBridge.Assignment) : Prop :=
 Models state model ∧ HeadModels effect.plan.packet model ∧
 SchemaHolds effect.plan effect.plan.headSchema model ∧ Outputs effect.plan model ∧
 (∀ clause ∈ effect.plan.packet.declaration.requirements, ∀ signature : clause.Signature roles,
   (childSchema effect.plan clause signature).Holds (variables effect.plan model) model) ∧
 effect.Live state.core model

theorem installation_models_iff
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry)
 (snapshot : effect.snapshot = state.core) :
 GeneralNominalVersionedInstall232.InstallationModels state effect model ↔ Residual state effect model := by
 rw [GeneralNominalVersionedMixedCommon235.installation_models_iff checked path registryEq snapshot]
 have frame : GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
     state.core effect.plan.packet.site.occurrence effect.plan.packet.declaration.id effect.plan :=
   registryEq ▸ snapshot ▸ effect.frame
 constructor
 · rintro ⟨valid,held,live⟩
   obtain ⟨head,schema,outputs,children⟩ := (GeneralNominalVersionedChildClosure237.source_holds_iff
     state effect.plan model path frame valid).mp held
   exact ⟨valid,head,schema,outputs,children,live⟩
 · rintro ⟨valid,head,schema,outputs,children,live⟩
   exact ⟨valid,(GeneralNominalVersionedChildClosure237.source_holds_iff
     state effect.plan model path frame valid).mpr ⟨head,schema,outputs,children⟩,live⟩

theorem source_installable_iff
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence
   (.selected key children))
 (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry)
 (snapshot : effect.snapshot = state.core) :
 GeneralNominalVersionedMixedKernel234.Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect ↔
 GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
 ∃ model, Residual state effect model := by
 rw [GeneralNominalVersionedMixedSelectedEffect235.source_installable_iff path selected registryEq snapshot]
 apply and_congr Iff.rfl
 exact exists_congr (fun model => installation_models_iff checked path registryEq snapshot)
end Yulang.GeneralNominalVersionedMixedMaterialization237
