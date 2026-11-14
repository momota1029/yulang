import Yulang.GeneralNominalInstalledEvidence190

/-! Existing ordinary-context transport instantiated at the actual WF boundary.
The relation below restricts real steps; descriptor-changing refresh is not
silently included. Every model in a conclusion is the same final assignment. -/
namespace Yulang.GeneralNominalOrdinaryEvidence191
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralDictionaryOrdinaryTrace (Extension)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {before after : State roles} {plan : Plan roles} {support : List (Occurrence roles)}

/-- A genuine WF step with exact ordinary-only growth of the inspection context. -/
def OrdinaryStep (registry : Registry) (root : Occurrence roles)
    (before after : State roles) : Prop :=
  (boundary roles).Step registry root before after ∧
  Extension before.core.erased.current.context after.core.erased.current.context

theorem trace_growth (path : B4Target.Steps (OrdinaryStep registry root) before after) :
    Extension before.core.erased.current.context after.core.erased.current.context := by
  induction path with
  | refl => exact GeneralDictionaryOrdinaryTrace.extension_refl _
  | tail _ action ih => exact GeneralDictionaryOrdinaryTrace.extension_trans ih action.2

theorem trace_steps (path : B4Target.Steps (OrdinaryStep registry root) before after) :
    B4Target.Steps ((boundary roles).Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ action ih => exact .tail ih action.1

theorem trace_models (path : B4Target.Steps (OrdinaryStep registry root) before after)
    (model : Assignment) (valid : Models after model) : Models before model :=
  steps_models (trace_steps path) model valid

/-- Both evidence judgments refer to precisely the same given final model. -/
theorem evidence_iff (path : B4Target.Steps (OrdinaryStep registry root) before after)
    (model : Assignment) (valid : Models after model) (demand : Occurrence roles) (payload : Payload) :
    (boundary roles).Evidence registry after model demand payload ↔
    (boundary roles).Evidence registry before model demand payload := by
  constructor
  · exact GeneralDictionaryOrdinaryTrace.evidence_extension_backward registry _ _
      (trace_growth path) model demand payload
  · exact GeneralDictionaryOrdinaryTrace.evidence_extension registry _ _
      (trace_growth path) model valid.1.1.1 demand payload

/-- Universal evidence is transported by restricting the final model, not by
selecting a different existential assignment. -/
theorem universal_evidence (path : B4Target.Steps (OrdinaryStep registry root) before after)
    (demand : Occurrence roles) (payload : Payload)
    (source : ∀ model, Models before model →
      (boundary roles).Evidence registry before model demand payload) :
    ∀ model, Models after model → (boundary roles).Evidence registry after model demand payload := by
  intro model valid
  exact (evidence_iff path model valid demand payload).mpr (source model (trace_models path model valid))

theorem install_growth (enabled : Installable registry before plan support) :
    Extension before.core.erased.current.context
      (install before plan support enabled).core.erased.current.context := by
  change Extension before.core.erased.current.context plan.packet.privateContext
  rw [← enabled.frame.context_eq]
  exact GeneralDictionaryOrdinaryTrace.packet_extension plan.packet

/-- Installability alone does not assert a step: generated focus and novelty
are retained explicitly. -/
theorem install_step (enabled : Installable registry before plan support)
    (reached : GeneralNominalSaturationState.Generated before.core.erased.current root plan.packet.site.occurrence)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before.core.erased.current plan.packet) :
    OrdinaryStep registry root before (install before plan support enabled) :=
  ⟨⟨plan.packet.site.occurrence,reached,.install plan support enabled novel⟩,install_growth enabled⟩

theorem installed_trace_instance (enabled : Installable registry before plan support)
    (path : B4Target.Steps (OrdinaryStep registry root)
      (install before plan support enabled) after)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.core.erased.current.context model
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children := by
  have source := GeneralNominalInstalledEvidence190.current_instance enabled model (trace_models path model valid)
  exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ (trace_growth path)
    model valid.1.1.1 _ _ _ source

theorem installed_trace_evidence (enabled : Installable registry before plan support)
    (path : B4Target.Steps (OrdinaryStep registry root)
      (install before plan support enabled) after)
    (model : Assignment) (valid : Models after model) (dictionaries : List Payload)
    (children : All₂ ((boundary roles).Evidence registry after model) plan.packet.children dictionaries) :
    (boundary roles).Evidence registry after model plan.packet.site.occurrence
      (.node plan.packet.declaration.id dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry _ model _ _ _ _
    (installed_trace_instance enabled path model valid) children

theorem installed_trace_terminal (enabled : Installable registry before plan support)
    (path : B4Target.Steps (OrdinaryStep registry root)
      (install before plan support enabled) after)
    (terminal : plan.packet.children = [])
    (model : Assignment) (valid : Models after model) :
    (boundary roles).Evidence registry after model plan.packet.site.occurrence
      (.node plan.packet.declaration.id []) := by
  apply installed_trace_evidence enabled path model valid []
  rw [terminal]
  exact .nil

end Yulang.GeneralNominalOrdinaryEvidence191
