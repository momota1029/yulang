import Yulang.GeneralNominalInitialLeafEvidence189

/-! Actual head-step installation yields a source instance in every current
model once stability forces commitment. This works at any generated occurrence,
with arbitrary children and named requests, without an initial-state premise.
Installation remains a genuine hypothesis: current selection alone does not
establish its common-model, materialization, choice or support fields. -/
namespace Yulang.GeneralNominalInstallableEvidence190
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
variable {plan : Plan roles} {support : List (Occurrence roles)}

/-- The class request list retains the packet occurrence's own requests.
The remaining generation guard is the actual installation field. -/
theorem request_ready (enabled : Installable registry state plan support) :
    GeneralNominalRecursiveCandidates.RequestReady plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds := by
  constructor
  · intro output member
    exact enabled.ready.1 output (request_retained plan.packet.site enabled.frame.raw_recorded (.refl _) member)
  · exact enabled.materialized

/-- Stability at a root forces semantic commitment at each generated,
installation-enabled occurrence. -/
theorem generated_committed (root : Occurrence roles)
    (stable : (boundary roles).Stable registry state root)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence)
    (enabled : Installable registry state plan support) :
    GeneralNominalFeedbackSteps.Committed state.core.erased.current plan.packet := by
  classical
  apply Classical.byContradiction
  intro novel
  exact stable plan.packet.site.occurrence generated _ (.install plan support enabled novel)

/-- No model is changed: the source instance is obtained in the given current
model, for the complete canonical child list of the packet. -/
theorem committed_instance (enabled : Installable registry state plan support)
    (committed : GeneralNominalFeedbackSteps.Committed state.core.erased.current plan.packet)
    (model : Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children := by
  have frame := enabled.frame
  have instanceRule : GeneralDictionaryRecursiveEvidence.Instance plan.packet.registry plan.packet.context model
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children := by
    refine ⟨plan.packet.declaration,?_,plan.packet.checked,rfl,?_,plan.packet.bounds,?_,?_,
      request_ready enabled,rfl,?_,?_⟩
    · simpa only [frame.registry_eq] using frame.visible
    · exact frame.role_eq
    · exact frame.located
    · have prepared := frame.prepared
      rw [← frame.context_eq] at prepared
      obtain ⟨_,_,_,bounds,found,finished,_⟩ := prepared
      have same := Option.some.inj (frame.located.symm.trans found)
      subst bounds
      exact finished
    · simpa only [frame.registry_eq,frame.context_eq] using frame.prepared.1
    · exact committed.1 model valid.1.1
  simpa only [frame.registry_eq,frame.context_eq] using instanceRule

/-- Arbitrary children are accepted only with their actual Evidence in the
same current context and model. This is an installation-conditional bridge,
not the general reachable-state EvidenceNode theorem. -/
theorem generated_evidence (root : Occurrence roles)
    (stable : (boundary roles).Stable registry state root)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence)
    (enabled : Installable registry state plan support)
    (model : Assignment) (valid : Models state model) (dictionaries : List Payload)
    (children : All₂ ((boundary roles).Evidence registry state model) plan.packet.children dictionaries) :
    (boundary roles).Evidence registry state model plan.packet.site.occurrence
      (.node plan.packet.declaration.id dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry state.core.erased.current.context model
    plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children dictionaries
    (committed_instance enabled (generated_committed root stable generated enabled) model valid) children

end Yulang.GeneralNominalInstallableEvidence190
