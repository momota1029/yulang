import Yulang.GeneralDictionarySharedInstallEvidence
import Yulang.GeneralDictionaryOrdinaryTrace

/-! The certified-origin emitter changes packet.privateContext, but that exact
change is an ordinary inspection-preserving extension. This supplies the missing
current-context bridge without identifying stored and private contexts, and
without converting the Shared transition into the old feedback transition. -/
namespace Yulang.GeneralDictionarySharedCurrentEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

theorem private_extension (packet : Packet roles) (support : List (Occurrence roles)) :
    GeneralDictionaryOrdinaryTrace.Extension packet.context
      (GeneralNominalSharedSteps.install state packet support).current.context :=
  GeneralDictionaryOrdinaryTrace.packet_extension packet

/-- Every actual successor model witnesses the CURRENT inspection instance. -/
theorem current_instance (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (model : Assignment)
    (valid : Models (GeneralNominalSharedSteps.install state packet support).current model) :
    Instance registry (GeneralNominalSharedSteps.install state packet support).current.context model
      packet.site.occurrence packet.declaration.id packet.children :=
  GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ (private_extension packet support)
    model valid.1 _ _ _
    (GeneralDictionarySharedInstallEvidence.installed_instance packet support enabled model valid)

/-- Recursive child evidence must be supplied at the same current context and
same final model; it is not replaced by mere packet membership or settlement. -/
theorem current_evidence (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (model : Assignment)
    (valid : Models (GeneralNominalSharedSteps.install state packet support).current model)
    (dictionaries : List Payload)
    (children : All₂ (Evidence registry (GeneralNominalSharedSteps.install state packet support).current.context model)
      packet.children dictionaries) :
    Evidence registry (GeneralNominalSharedSteps.install state packet support).current.context model
      packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  evidence_node _ _ _ _ _ _ _ (current_instance packet support enabled model valid) children

theorem terminal_current_evidence (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (terminal : packet.children = []) (model : Assignment)
    (valid : Models (GeneralNominalSharedSteps.install state packet support).current model) :
    Evidence registry (GeneralNominalSharedSteps.install state packet support).current.context model
      packet.site.occurrence (.node packet.declaration.id []) := by
  apply current_evidence packet support enabled model valid []
  rw [terminal]
  exact .nil

/-- A genuine guarded Shared transition plus its final current-context terminal
dictionary. All execution side conditions are separate from the conclusion. -/
theorem actual_terminal_current_dictionary (root : Occurrence roles) (packet : Packet roles)
    (support : List (Occurrence roles))
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet)
    (guard : GeneralNominalSharedSteps.PacketGuard state packet support)
    (terminal : packet.children = []) :
    GeneralNominalSharedSteps.Step registry root state (GeneralNominalSharedSteps.install state packet support) ∧
    ∀ model, Models (GeneralNominalSharedSteps.install state packet support).current model →
      Evidence registry (GeneralNominalSharedSteps.install state packet support).current.context model
        packet.site.occurrence (.node packet.declaration.id []) :=
  ⟨⟨packet.site.occurrence,generated,.install packet support enabled novel guard⟩,
   fun model valid => terminal_current_evidence packet support enabled terminal model valid⟩
end Yulang.GeneralDictionarySharedCurrentEvidence
