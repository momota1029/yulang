import Yulang.GeneralDictionaryFinishedTrace

/-! Current-context semantics of all packets along actual restricted feedback
traces. Unlike a single-record transport lemma, no original-context Extension
premise is required for each final packet. Same-carrier/fixed-view refreshes remain
explicit in the existing trace relation. No stable-selection coverage is claimed. -/
namespace Yulang.GeneralDictionaryCurrentJournal
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryFinishedTrace

/-- An invariant to prove by trace induction, not a new source assumption. -/
def Current (registry : Registry) (state : State roles) : Prop :=
  ∀ packet ∈ state.packets, ∀ model, Models state model →
    GeneralDictionaryRecursiveEvidence.Instance registry state.context model
      packet.site.occurrence packet.declaration.id packet.children

theorem initial_current (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Current registry (initial context root) := by
  intro packet member
  cases member

/-- The actual enabled installation supplies the new packet's current Instance. -/
theorem installed_current (registry : Registry) (before : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry before packet)
    (model : Assignment)
    (valid : Models (GeneralNominalFeedbackSites.install before packet
      (GeneralNominalFeedbackSites.emitted packet)) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry
      (GeneralNominalFeedbackSites.install before packet
        (GeneralNominalFeedbackSites.emitted packet)).context model
      packet.site.occurrence packet.declaration.id packet.children := by
  have rule := GeneralDictionaryOrdinaryTrace.installed_trace_current_instance
    registry packet.site.occurrence before _ packet enabled .refl model valid
  rw [enabled.1.1] at rule
  exact rule

theorem step_current (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (step : Step registry root before after)
    (current : Current registry before) : Current registry after := by
  have retain : ∀ packet ∈ before.packets, ∀ model, Models after model →
      GeneralDictionaryRecursiveEvidence.Instance registry after.context model
        packet.site.occurrence packet.declaration.id packet.children := by
    intro packet member model valid
    have earlier := GeneralNominalFeedbackSteps.step_models
      (step_feedback registry root before after step) model valid
    exact step_instance registry root packet.site.occurrence before after step model valid
      packet.declaration.id packet.children (current packet member model earlier)
  intro packet member model valid
  cases step with
  | refresh next view certificate actual => exact retain packet member model valid
  | ordinary actual =>
    obtain ⟨focus,generated,action⟩ := actual.1
    cases action with
    | enqueue => exact retain packet member model valid
    | merge => exact retain packet member model valid
    | refresh => exact retain packet member model valid
    | equate => exact retain packet member model valid
    | install installed enabled novel =>
      rcases List.mem_cons.mp member with rfl | old
      · exact installed_current registry before packet enabled model valid
      · exact retain packet old model valid

theorem trace_current (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after)
    (current : Current registry before) : Current registry after := by
  induction path with
  | refl => exact current
  | tail _ step ih => exact step_current registry root _ _ step ih

/-- From an empty journal, all actual recorded packets have current-context
meaning, even if refreshes occur before and after later installations. -/
theorem initial_trace_current (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : State roles)
    (path : B4Target.Steps (Step registry root) (initial context root) after) :
    Current registry after :=
  trace_current registry root _ after path (initial_current registry context root)

theorem recorded_node (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : State roles)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (packet : Packet roles) (recorded : packet ∈ after.packets)
    (model : Assignment) (valid : Models after model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (children : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry after.context model)
      packet.children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.context model
      packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry after.context model
    packet.site.occurrence packet.declaration.id packet.children dictionaries
    (initial_trace_current registry root context after path packet recorded model valid) children

end Yulang.GeneralDictionaryCurrentJournal
