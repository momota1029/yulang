import Yulang.GeneralDictionaryDefaultReinspection209

set_option backward.isDefEq.respectTransparency false

/-! Configuration equality follows from the corrected trace; report equality
and equal input centers remain separate, visible reinspection obligations. -/
namespace Yulang.GeneralDictionaryDefaultConfiguration209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepHistory (Built)
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles}

 theorem seed (built : Built value context root state) :
    state.core.erased.current.context.state.seed = context.state.seed := by
  induction built with
  | initial => rfl
  | install prior effect snapshot registryEq ih =>
      have ctx := effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snapshot)
      exact (congrArg (fun context : GeneralNominalCandidates.Context => context.state.seed) ctx).trans ih
  | merge _ _ _ _ ih => exact ih
  | context _ _ same _ ih => exact same.trans ih

 theorem frame_constructors
    (frame : GeneralNominalCenteredHeadOutputs.Frame value core focus key plan) :
    plan.packet.context.state.constructors = value.constructors := by
  rw [frame.context_eq]
  exact frame.prepared.1.1.symm

 theorem stored (built : Built value context root state) (member : plan ∈ state.core.plans) :
    plan.packet.registry = value ∧ plan.packet.context.state.seed = context.state.seed ∧
      plan.packet.context.interpretation = context.interpretation ∧
      plan.packet.context.state.constructors = value.constructors := by
  induction built with
  | initial => cases member
  | install prior effect snapshot registryEq ih =>
      rcases List.mem_cons.mp member with rfl | member
      · have ctx := effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snapshot)
        exact ⟨effect.frame.registry_eq.trans registryEq,
          (congrArg (fun context : GeneralNominalCandidates.Context => context.state.seed) ctx).trans (seed prior),
          (congrArg GeneralNominalCandidates.Context.interpretation ctx).trans
            (GeneralNominalCenteredHeadMatStepHistory.interpretation prior),
          (frame_constructors effect.frame).trans (congrArg Registry.constructors registryEq)⟩
      · exact ih member
  | merge _ _ _ _ ih => exact ih member
  | context _ _ _ _ ih => exact ih member

 theorem reinspection_data
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (declaration : current.packet.declaration = historical.packet.declaration)
    (input : current.input = historical.input)
    (report : GeneralNominalReportErasure.erase current.packet.context.state
        (GeneralNominalPacketSupport.report current.packet) =
      GeneralNominalReportErasure.erase historical.packet.context.state
        (GeneralNominalPacketSupport.report historical.packet)) :
    GeneralNominalCenteredHeadMatPlanData.Same current historical := by
  obtain ⟨start,initial,path⟩ := reachable
  have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
  have built := GeneralDictionaryDefaultTrace208.built_trace path
  have old := stored built member
  exact ⟨frame.registry_eq.trans old.1.symm,declaration,input,
    ((congrArg (fun context : GeneralNominalCandidates.Context => context.state.seed) frame.context_eq).trans
      (seed built)).trans old.2.1.symm,
    (frame_constructors frame).trans old.2.2.2.symm,
    ((congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).trans
      (GeneralNominalCenteredHeadMatStepHistory.interpretation built)).trans old.2.2.1.symm,report⟩

end Yulang.GeneralDictionaryDefaultConfiguration209
