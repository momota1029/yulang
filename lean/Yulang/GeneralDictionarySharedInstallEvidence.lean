import Yulang.GeneralNominalSharedSteps
import Yulang.GeneralDictionaryCommittedEvidence

/-! Evidence for the actual certified-origin emitter. This is not a conversion
of Shared Stable into older Settled Stable. Guard and installability remain
explicit; nonterminal child evidence remains explicit. -/
namespace Yulang.GeneralDictionarySharedInstallEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

/-- Actual Shared stability commits only genuinely enabled, guarded packets. -/
theorem stable_committed {root : Occurrence roles} (packet : Packet roles)
    (stable : GeneralNominalSharedSteps.Stable registry state root)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (support : List (Occurrence roles))
    (guard : GeneralNominalSharedSteps.PacketGuard state packet support) :
    GeneralNominalFeedbackSteps.Committed state.current packet := by
  classical
  exact Classical.byContradiction (fun novel =>
    stable packet.site.occurrence generated _ (.install packet support enabled novel guard))

/-- Source instance in the packet stored inspection context, valid in every
actual Shared successor model. The successor private context is not identified
with this stored context. -/
theorem installed_instance (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (model : Assignment)
    (valid : Models (GeneralNominalSharedSteps.install state packet support).current model) :
    Instance registry packet.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  have instanceRule := GeneralDictionaryCommittedEvidence.committed_instance
    (GeneralNominalSharedSteps.install state packet support).current packet
    (by simpa only [enabled.1.1] using enabled.1.2.2.2.1)
    enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 enabled.1.2.2.2.2.2.2.1
    (GeneralNominalSharedSteps.installed_committed state packet support) model valid
  simpa only [enabled.1.1] using instanceRule

/-- Shared-emitter child edges are genuinely present in the successor. -/
theorem installed_children (packet : Packet roles) (support : List (Occurrence roles)) :
    ∀ child ∈ packet.children,
      Generated (GeneralNominalSharedSteps.install state packet support).current packet.site.occurrence child :=
  GeneralDictionaryCommittedEvidence.committed_children _ packet
    (GeneralNominalSharedSteps.installed_committed state packet support)

theorem installed_evidence (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (model : Assignment) (valid : Models (GeneralNominalSharedSteps.install state packet support).current model)
    (dictionaries : List Payload)
    (children : All₂ (Evidence registry packet.context model)
      packet.children dictionaries) :
    Evidence registry packet.context model
      packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  evidence_node _ _ _ _ _ _ _ (installed_instance packet support enabled model valid) children

/-- Terminal actual Shared installations need no assumed child evidence. -/
theorem terminal_evidence (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (terminal : packet.children = []) (model : Assignment)
    (valid : Models (GeneralNominalSharedSteps.install state packet support).current model) :
    Evidence registry packet.context model
      packet.site.occurrence (.node packet.declaration.id []) := by
  apply installed_evidence packet support enabled model valid []
  rw [terminal]
  exact .nil
/-- Actual guarded novel installation and its all-model stored-context evidence.
The children premise is needed only for the nonterminal recursive case. -/
theorem actual_terminal_step (root : Occurrence roles) (packet : Packet roles)
    (support : List (Occurrence roles))
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet)
    (guard : GeneralNominalSharedSteps.PacketGuard state packet support)
    (terminal : packet.children = []) :
    GeneralNominalSharedSteps.Step registry root state
      (GeneralNominalSharedSteps.install state packet support) ∧
    ∀ model, Models (GeneralNominalSharedSteps.install state packet support).current model →
      Evidence registry packet.context model packet.site.occurrence (.node packet.declaration.id []) := by
  exact ⟨⟨packet.site.occurrence,generated,.install packet support enabled novel guard⟩,
    fun model valid => terminal_evidence packet support enabled terminal model valid⟩

/-- Stable actual Shared closure yields evidence for an enabled terminal packet
in its stored/current inspection context, rather than its private successor context. -/
theorem stable_terminal_evidence (root : Occurrence roles) (packet : Packet roles)
    (support : List (Occurrence roles))
    (stable : GeneralNominalSharedSteps.Stable registry state root)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : GeneralNominalSharedSteps.PacketGuard state packet support)
    (terminal : packet.children = []) (model : Assignment) (valid : Models state.current model) :
    Evidence registry state.current.context model packet.site.occurrence (.node packet.declaration.id []) := by
  have committed := stable_committed packet stable generated enabled support guard
  have inst := GeneralDictionaryCommittedEvidence.committed_instance state.current packet
    (by simpa only [enabled.1.1] using enabled.1.2.2.2.1)
    enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 enabled.1.2.2.2.2.2.2.1 committed model valid
  have current : Instance registry state.current.context model packet.site.occurrence packet.declaration.id [] := by
    simpa only [enabled.1.1,enabled.1.2.1,terminal] using inst
  exact evidence_node _ _ _ _ _ _ _ current .nil
end Yulang.GeneralDictionarySharedInstallEvidence
