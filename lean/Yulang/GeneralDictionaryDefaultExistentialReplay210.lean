import Yulang.GeneralDictionaryDefaultRetainedCenter210
import Yulang.GeneralDictionaryDefaultProduction208

set_option backward.isDefEq.respectTransparency false

/-! Arbitrary-interval stored-parent evidence. A current witness keeps the
recorded historical center, rather than equating unrelated interval points. -/
namespace Yulang.GeneralDictionaryDefaultExistentialReplay210
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary Local)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles} {current historical : Plan roles}

 theorem nominal_instance
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (refinement : GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Instance (registry value) state.core model focus key current.packet.children :=
  GeneralDictionaryDefaultRetainedCenter210.evidence_instance checked reachable frame member keyEq occurrence
    (GeneralDictionaryDefaultSemanticReplay209.nominal_report checked reachable frame member keyEq occurrence refinement shape) valid

 theorem nominal_evidence
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (refinement : GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (valid : Models state model)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model)
      current.packet.children dictionaries) :
    GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model focus (.node key dictionaries) :=
  GeneralDictionaryTotalEvidence206.evidence_node
    (nominal_instance checked reachable frame member keyEq occurrence refinement shape valid) given

/-- Selection supplies the current frame. The historical-frame compatibility
condition remains explicit and does not restrict the boundary's Local predicate. -/
 theorem selected_nominal_evidence
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (refinement : GeneralNominalRefinements.Refines historical.packet.context.state state.core.erased.current.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (valid : Models state model)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model)
      children dictionaries) :
    GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model focus (.node key dictionaries) := by
  obtain ⟨current,frame,kids⟩ := GeneralDictionaryDefaultAvailability208.selected_frame reachable selected
  apply nominal_evidence checked reachable frame member keyEq occurrence
    ((congrArg GeneralNominalCandidates.Context.state frame.context_eq).symm ▸ refinement) shape valid
  exact kids.symm ▸ given

 theorem selected_nominal_generated
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (refinement : GeneralNominalRefinements.Refines historical.packet.context.state state.core.erased.current.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (reached : focus = root ∨ (boundary roles).Generated value state root focus)
    (childMember : child ∈ children) : (boundary roles).Generated value state root child := by
  obtain ⟨current,frame,kids⟩ := GeneralDictionaryDefaultAvailability208.selected_frame reachable selected
  exact GeneralDictionaryDefaultSemanticReplay209.nominal_generated_children checked reachable frame member keyEq occurrence
    ((congrArg GeneralNominalCandidates.Context.state frame.context_eq).symm ▸ refinement) shape reached (kids.symm ▸ childMember)

end Yulang.GeneralDictionaryDefaultExistentialReplay210
