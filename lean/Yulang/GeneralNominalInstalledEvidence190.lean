import Yulang.GeneralNominalInstallableEvidence190
import Yulang.GeneralDictionaryOrdinaryTrace

/-! Actual WF head installation yields current-context Evidence, using the
existing ordinary-extension transport. No Initial or Stable premise is needed.
Nonleaf evidence explicitly retains child evidence in the same successor model. -/
namespace Yulang.GeneralNominalInstalledEvidence190
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalInstallableEvidence190 (request_ready)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
variable {plan : Plan roles} {support : List (Occurrence roles)}

theorem stored_instance (enabled : Installable registry state plan support)
    (model : Assignment) (valid : plan.packet.Holds model) :
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
    · exact valid
  simpa only [frame.registry_eq,frame.context_eq] using instanceRule

theorem current_instance (enabled : Installable registry state plan support)
    (model : Assignment) (valid : Models (install state plan support enabled) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry
      (install state plan support enabled).core.erased.current.context model
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children := by
  have branch := ((install_models enabled model).mp valid).2.1.1
  have old := stored_instance enabled model branch
  rw [← enabled.frame.context_eq] at old
  exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _
    (GeneralDictionaryOrdinaryTrace.packet_extension plan.packet) model valid.1.1.1 _ _ _ old

theorem current_evidence (enabled : Installable registry state plan support)
    (model : Assignment) (valid : Models (install state plan support enabled) model)
    (dictionaries : List Payload)
    (children : All₂ ((boundary roles).Evidence registry (install state plan support enabled) model)
      plan.packet.children dictionaries) :
    (boundary roles).Evidence registry (install state plan support enabled) model
      plan.packet.site.occurrence (.node plan.packet.declaration.id dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry _ model _ _ _ _
    (current_instance enabled model valid) children

theorem terminal_evidence (enabled : Installable registry state plan support)
    (terminal : plan.packet.children = [])
    (model : Assignment) (valid : Models (install state plan support enabled) model) :
    (boundary roles).Evidence registry (install state plan support enabled) model
      plan.packet.site.occurrence (.node plan.packet.declaration.id []) := by
  apply current_evidence enabled model valid []
  rw [terminal]
  exact .nil

end Yulang.GeneralNominalInstalledEvidence190
