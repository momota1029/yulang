import Yulang.GeneralDictionaryDefaultBoundary208

namespace Yulang.GeneralDictionaryDefaultCommitment208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultKernel208
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles} {plan : Plan roles}
  {model : Assignment} {root : Occurrence roles}

/-- Every output in the entire current alias class is enforced, whether or not
its parent's children had already been recorded. -/
theorem committed_output (committed : Committed state plan)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready state.core plan.packet.site.occurrence plan)
    (valid : Models state model)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state.core plan.packet.site.occurrence) :
    GeneralDictionaryDefaultEvidence204.OutputWitness plan model output :=
  GeneralDictionaryDefaultEvidence204Laws.output_of_class_effects ready
    (committed_class committed valid) member

theorem alias_output (committed : Committed state plan)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready state.core plan.packet.site.occurrence plan)
    (valid : Models state model)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      root.identity plan.packet.site.occurrence.identity)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state.core root) :
    GeneralDictionaryDefaultEvidence204.OutputWitness plan model output :=
  committed_output committed ready valid
    ((GeneralNominalCenteredHeadOutputs.same_class_requests alias).mp member)

theorem equal_named_outputs (committed : Committed state plan) (valid : Models state model)
    (one : first ∈ GeneralNominalCenteredHeadOutputs.requests state.core plan.packet.site.occurrence)
    (two : last ∈ GeneralNominalCenteredHeadOutputs.requests state.core plan.packet.site.occurrence)
    (named : first.name = last.name) :
    CommonNominalFullCarrier.Equivalent (model first.target).1 (model last.target).1 :=
  (committed_class committed valid).2 first one last two named

theorem certificate (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core root key plan)
    (committed : Committed state plan)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready state.core root plan)
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Certificate registry state.core model root key plan.packet.children plan :=
  GeneralDictionaryTotalEvidence206.certificate_of_semantics frame rfl
    (committed.1.1 model valid) ready (frame.occurrence_eq ▸ committed_class committed valid)

theorem enabled_stable_committed (enabled : Installable registry state effect)
    (stable : Stable registry state effect.plan.packet.site.occurrence) : Committed state effect.plan := by
  classical
  apply Classical.byContradiction
  intro novel
  exact stable _ .root _ (.install effect enabled novel)

/-- Conditional local assembly, not the global EvidenceNode: availability is an
explicit remaining obligation rather than disguised as a selected-input guard. -/
theorem enabled_stable_node (enabled : Installable registry state effect)
    (stable : Stable registry state effect.plan.packet.site.occurrence)
    (valid : Models state model)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryTotalEvidence206.Evidence registry state.core model)
      effect.plan.packet.children dictionaries) :
    GeneralDictionaryTotalEvidence206.Evidence registry state.core model
      effect.plan.packet.site.occurrence (.node effect.plan.packet.declaration.id dictionaries) := by
  apply GeneralDictionaryTotalEvidence206.evidence_node _ given
  exact ⟨effect.plan,certificate
    (enabled.snapshot_eq ▸ enabled.registry_eq ▸ effect.frame)
    (enabled_stable_committed enabled stable) (enabled.snapshot_eq ▸ effect.ready) valid⟩

end Yulang.GeneralDictionaryDefaultCommitment208
