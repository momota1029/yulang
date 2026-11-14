import Yulang.GeneralNominalInstalledForest191

/-! Reusing semantically committed packets at the actual WF boundary.
This does not manufacture a transition or select a fresh model. -/
namespace Yulang.GeneralNominalCommittedEvidence192
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalOrdinaryEvidence191
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {before after : State roles} {plan : Plan roles} {support : List (Occurrence roles)}

theorem trace_evidence (enabled : Installable registry before plan support)
    (committed : GeneralNominalFeedbackSteps.Committed before.core.erased.current plan.packet)
    (path : B4Target.Steps (OrdinaryStep registry root) before after)
    (model : Assignment) (valid : Models after model) (payloads : List Payload)
    (children : All₂ ((boundary roles).Evidence registry after model) plan.packet.children payloads) :
    (boundary roles).Evidence registry after model plan.packet.site.occurrence
      (.node plan.packet.declaration.id payloads) := by
  have old := GeneralNominalInstallableEvidence190.committed_instance enabled committed model (trace_models path model valid)
  have current := GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ (trace_growth path)
    model valid.1.1.1 _ _ _ old
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry _ model _ _ _ _ current children

theorem generated_child (committed : GeneralNominalFeedbackSteps.Committed before.core.erased.current plan.packet)
    (reached : GeneralNominalSaturationState.Generated before.core.erased.current root plan.packet.site.occurrence)
    (child : Occurrence roles) (member : child ∈ plan.packet.children) :
    GeneralNominalSaturationState.Generated before.core.erased.current root child :=
  .child reached (committed.2 child member)

end Yulang.GeneralNominalCommittedEvidence192
