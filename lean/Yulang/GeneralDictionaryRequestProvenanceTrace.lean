import Yulang.GeneralDictionaryRequestProvenance
import Yulang.GeneralNominalValueBudget

/-! Request provenance survives every actual Value transition, including
reobservation and captured-value feedback. This is syntactic provenance
transport, not preservation of an arbitrary selected candidate. -/
namespace Yulang.GeneralDictionaryRequestProvenanceTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalMaterialization
open GeneralDictionaryRequestProvenance
variable {roles : Roles.RoleDecls}

theorem recorded_step (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles) (step : GeneralNominalValueSteps.Step registry root before after)
    (batch : List Request) (covered : GeneralDictionaryRecordedBatchModels.Covered before.current batch) :
    GeneralDictionaryRecordedBatchModels.Covered after.current batch := by
  intro request member
  obtain ⟨packet,present,requestMember,closed⟩ := covered request member
  exact ⟨packet,GeneralNominalValueBudget.at_packets step.choose_spec.2 packet present,requestMember,closed⟩

theorem supported_step (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles) (step : GeneralNominalValueSteps.Step registry root before after)
    (batch : List Request) (supported : Supported registry root before batch) :
    Supported registry root after batch := by
  intro request member
  rcases supported request member with ⟨earlier,reachable,path,observed⟩ | recorded
  · exact Or.inl ⟨earlier,reachable,.tail path step,observed⟩
  · exact Or.inr (recorded_step registry root before after step [request] recorded)

theorem supported_trace (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after)
    (batch : List Request) (supported : Supported registry root before batch) :
    Supported registry root after batch := by
  induction path with
  | refl => exact supported
  | tail _ step ih => exact supported_step registry root _ _ step batch ih

theorem reachable_trace (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root before)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after) :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root after := by
  induction path with
  | refl => exact reachable
  | tail _ step ih =>
    obtain ⟨start,initial,priorPath⟩ := ih
    exact ⟨start,initial,.tail priorPath step⟩

theorem models_after_trace (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root before)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after)
    (batch : List Request) (supported : Supported registry root before batch)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    GeneralNominalMaterialization.Models after.current.context.state declaration capture report
      (generated after.current.context.state after.current.context.interpretation batch) model :=
  models registry root after (reachable_trace registry root before after reachable path) batch
    (supported_trace registry root before after path batch supported) declaration capture report model valid
end Yulang.GeneralDictionaryRequestProvenanceTrace
