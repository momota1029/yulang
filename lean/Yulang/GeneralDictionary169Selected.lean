import Yulang.GeneralDictionaryRecorded168Relocation
import Yulang.GeneralDictionarySelectedInstanceCoherence
import Yulang.GeneralDictionarySharedInstallEvidence
import Yulang.GeneralDictionarySharedRecursiveExample

/-! Same-current selected node assembly. Historical coverage and relocation
remain explicit; Shared stability is used only with the actual full guard. -/
namespace Yulang.GeneralDictionary169Selected
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

theorem relocated_selected {root : Occurrence roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (relocation : GeneralDictionaryRecorded168Relocation.Relocates registry state packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (selected : GeneralNominalFeedbackK2.Local registry state.current packet.site.occurrence
      (.selected key children)) :
    packet.declaration.id = key ∧ packet.children = children :=
  GeneralDictionarySelectedInstanceCoherence.instance_selected registry state.current
    packet.site.occurrence model packet.declaration.id key packet.children children
    (GeneralDictionaryRecorded168Relocation.current_instance formed packet member relocation model valid) selected

theorem relocated_selected_evidence {root : Occurrence roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (relocation : GeneralDictionaryRecorded168Relocation.Relocates registry state packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (selected : GeneralNominalFeedbackK2.Local registry state.current packet.site.occurrence
      (.selected key children)) (payloads : List Payload)
    (dictionaries : All₂ (Evidence registry state.current.context model) children payloads) :
    Evidence registry state.current.context model packet.site.occurrence (.node key payloads) := by
  obtain ⟨sameKey,sameChildren⟩ := relocated_selected formed packet member relocation model valid selected
  have inst := GeneralDictionaryRecorded168Relocation.current_instance formed packet member relocation model valid
  rw [sameKey,sameChildren] at inst
  exact evidence_node _ _ _ _ _ _ _ inst dictionaries

theorem stable_current_instance {root : Occurrence roles} (packet : Packet roles)
    (stable : GeneralNominalSharedSteps.Stable registry state root)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (support : List (Occurrence roles))
    (guard : GeneralNominalSharedSteps.PacketGuard state packet support)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model packet.site.occurrence packet.declaration.id packet.children := by
  have committed := GeneralDictionarySharedInstallEvidence.stable_committed packet stable generated enabled support guard
  have inst := GeneralDictionaryCommittedEvidence.committed_instance state.current packet
    (by simpa only [enabled.1.1] using enabled.1.2.2.2.1)
    enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 enabled.1.2.2.2.2.2.2.1 committed model valid
  simpa only [enabled.1.1,enabled.1.2.1] using inst

theorem stable_generated_children {root : Occurrence roles} (packet : Packet roles)
    (stable : GeneralNominalSharedSteps.Stable registry state root)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (support : List (Occurrence roles))
    (guard : GeneralNominalSharedSteps.PacketGuard state packet support) :
    ∀ child ∈ packet.children, Generated state.current root child := by
  intro child member
  exact generated_trans generated
    (GeneralDictionaryCommittedEvidence.committed_children state.current packet
      (GeneralDictionarySharedInstallEvidence.stable_committed packet stable generated enabled support guard) child member)

theorem stable_current_evidence {root : Occurrence roles} (packet : Packet roles)
    (stable : GeneralNominalSharedSteps.Stable registry state root)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (support : List (Occurrence roles))
    (guard : GeneralNominalSharedSteps.PacketGuard state packet support)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (payloads : List Payload)
    (dictionaries : All₂ (Evidence registry state.current.context model) packet.children payloads) :
    Evidence registry state.current.context model packet.site.occurrence (.node packet.declaration.id payloads) :=
  evidence_node _ _ _ _ _ _ _
    (stable_current_instance packet stable generated enabled support guard model valid) dictionaries
/-- Finite child evidence existence is sufficient; no preassembled payload list
or parent Evidence is assumed. -/
theorem child_payloads (sites : List (Occurrence roles))
    (evidence : ∀ child ∈ sites, ∃ payload, Evidence registry state.current.context model child payload) :
    ∃ payloads, All₂ (Evidence registry state.current.context model) sites payloads := by
  induction sites with
  | nil => exact ⟨[],.nil⟩
  | cons child rest ih =>
    obtain ⟨payload,one⟩ := evidence child (by simp)
    obtain ⟨payloads,others⟩ := ih (fun next member => evidence next (by simp [member]))
    exact ⟨payload :: payloads,.cons one others⟩

/-- Actual post-install model and separate child existence produce a complete
nonterminal parent dictionary. This does not establish successor stability. -/
theorem installed_dictionary_exists (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models (GeneralNominalSharedSteps.install state packet support).current model)
    (children : ∀ child ∈ packet.children, ∃ payload,
      Evidence registry (GeneralNominalSharedSteps.install state packet support).current.context model child payload) :
    ∃ payloads, Evidence registry (GeneralNominalSharedSteps.install state packet support).current.context model
      packet.site.occurrence (.node packet.declaration.id payloads) := by
  obtain ⟨payloads,dictionaries⟩ := child_payloads packet.children children
  exact ⟨payloads,GeneralDictionarySharedCurrentEvidence.current_evidence packet support enabled model valid payloads dictionaries⟩

/-- Existing actual Display installation witnesses the new existential assembly
route with nonempty children. The dictionary and trace are not new examples. -/
theorem actual_nonterminal_exists :
    ∃ model, Models GeneralDictionarySharedDisplayInstallation.after.current model ∧
      ∃ payloads, payloads.length = 1 ∧ Evidence GeneralNominalExamples.registry
        GeneralDictionarySharedDisplayInstallation.after.current.context model
        GeneralNominalExamples.displayRoot (.node 1 payloads) := by
  obtain ⟨model,valid⟩ := GeneralDictionarySharedDisplayInstallation.inhabited
  refine ⟨model,valid,[.node 3 []],rfl,?_⟩
  apply GeneralDictionarySharedCurrentEvidence.current_evidence
    (state := GeneralDictionarySharedDisplayInstallation.start)
    (GeneralNominalSharedExamples.packet false) [] GeneralDictionarySharedDisplayInstallation.installable model valid
  rw [GeneralDictionarySharedDisplayInstallation.children]
  exact .cons (GeneralDictionarySharedRecursiveExample.leaf_evidence model valid) .nil
end Yulang.GeneralDictionary169Selected
