import Yulang.GeneralDictionarySharedCurrentEvidence

/-! Evidence transported along actual certified-origin Shared transitions.
All Shared continuations preserve the stored source instance. Only continuations
whose inspection contexts are ordinary extensions are used for current-context
transport; arbitrary descriptor-changing refresh is deliberately excluded. -/
namespace Yulang.GeneralDictionarySharedEvidenceTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryOrdinaryTrace (Extension)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls}

theorem trace_models (registry : Registry) (root : Occurrence roles) (before after : Tracked roles)
    (path : B4Target.Steps (GeneralNominalSharedSteps.Step registry root) before after)
    (model : Assignment) (valid : Models after.current model) : Models before.current model := by
  induction path with
  | refl => exact valid
  | tail prior step ih => exact ih (GeneralNominalSharedSteps.step_models step model valid)

/-- Every continuation, including reobservation, preserves the stored instance
for every surviving final model. No current-context transport is claimed here. -/
theorem stored_instance (registry : Registry) (root : Occurrence roles) (before after : Tracked roles)
    (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
    (path : B4Target.Steps (GeneralNominalSharedSteps.Step registry root)
      (GeneralNominalSharedSteps.install before packet support) after)
    (model : Assignment) (valid : Models after.current model) :
    Instance registry packet.context model packet.site.occurrence packet.declaration.id packet.children :=
  GeneralDictionarySharedInstallEvidence.installed_instance packet support enabled model
    (trace_models registry root _ after path model valid)

/-- A restriction of the actual Shared relation, not a replacement execution
rule and not a conversion into the legacy emitter's relation. -/
def OrdinaryStep (registry : Registry) (root : Occurrence roles) (before after : Tracked roles) : Prop :=
  GeneralNominalSharedSteps.Step registry root before after ∧ Extension before.current.context after.current.context

theorem ordinary_trace_real (registry : Registry) (root : Occurrence roles) (before after : Tracked roles)
    (path : B4Target.Steps (OrdinaryStep registry root) before after) :
    B4Target.Steps (GeneralNominalSharedSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih step.1

theorem ordinary_trace_extension (registry : Registry) (root : Occurrence roles) (before after : Tracked roles)
    (path : B4Target.Steps (OrdinaryStep registry root) before after) :
    Extension before.current.context after.current.context := by
  induction path with
  | refl => exact GeneralDictionaryOrdinaryTrace.extension_refl _
  | tail prior step ih => exact GeneralDictionaryOrdinaryTrace.extension_trans ih step.2

theorem current_instance (registry : Registry) (root : Occurrence roles) (before after : Tracked roles)
    (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
    (path : B4Target.Steps (OrdinaryStep registry root)
      (GeneralNominalSharedSteps.install before packet support) after)
    (model : Assignment) (valid : Models after.current model) :
    Instance registry after.current.context model packet.site.occurrence packet.declaration.id packet.children := by
  have stored := stored_instance registry root before after packet support enabled
    (ordinary_trace_real registry root _ after path) model valid
  exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _
    (GeneralDictionaryOrdinaryTrace.extension_trans
      (GeneralDictionarySharedCurrentEvidence.private_extension packet support)
      (ordinary_trace_extension registry root _ after path)) model valid.1 _ _ _ stored

theorem current_evidence (registry : Registry) (root : Occurrence roles) (before after : Tracked roles)
    (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
    (path : B4Target.Steps (OrdinaryStep registry root)
      (GeneralNominalSharedSteps.install before packet support) after)
    (model : Assignment) (valid : Models after.current model) (dictionaries : List Payload)
    (children : All₂ (Evidence registry after.current.context model) packet.children dictionaries) :
    Evidence registry after.current.context model packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  evidence_node _ _ _ _ _ _ _
    (current_instance registry root before after packet support enabled path model valid) children

/-- Generated focus, novelty and the certified guard supply the real first step;
the ordinary continuation already consists of actual Shared transitions. -/
theorem execution (registry : Registry) (root : Occurrence roles) (before after : Tracked roles)
    (packet : Packet roles) (support : List (Occurrence roles))
    (generated : Generated before.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current packet)
    (guard : GeneralNominalSharedSteps.PacketGuard before packet support)
    (path : B4Target.Steps (OrdinaryStep registry root)
      (GeneralNominalSharedSteps.install before packet support) after) :
    B4Target.Steps (GeneralNominalSharedSteps.Step registry root) before after := by
  have initial : GeneralNominalSharedSteps.Step registry root before
      (GeneralNominalSharedSteps.install before packet support) :=
    ⟨packet.site.occurrence,generated,.install packet support enabled novel guard⟩
  induction path with
  | refl => exact .tail .refl initial
  | tail prior step ih => exact .tail ih step.1
end Yulang.GeneralDictionarySharedEvidenceTrace
