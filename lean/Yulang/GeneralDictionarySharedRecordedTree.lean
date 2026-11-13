import Yulang.GeneralDictionarySharedRecordedEvidence
import Yulang.GeneralDictionarySharedTerminalInstallation
/-! Finite journal syntax, independent of Models, Instance and semantic Evidence.
Tree existence is not inferred from Stable or classification. Ordinary growth
is explicit in the semantic interpretation. -/
namespace Yulang.GeneralDictionarySharedRecordedTree
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)

inductive RecordedTree (state : State roles) : Occurrence roles → Payload → Prop
  | node (packet : Packet roles) (member : packet ∈ state.packets)
      (dictionaries : List Payload)
      (children : All₂ (RecordedTree state) packet.children dictionaries) :
      RecordedTree state packet.site.occurrence (.node packet.declaration.id dictionaries)

theorem discharged (tree : RecordedTree state occurrence payload) : Discharged state occurrence := by
  induction tree using RecordedTree.rec
    (motive_2 := fun sites _ _ => ∀ child ∈ sites, Discharged state child) with
  | node packet member dictionaries children ih => exact .packet packet member ih
  | nil => rename_i child member; cases member
  | cons one rest ihOne ihRest =>
    rename_i child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihOne
    · exact ihRest child member

theorem packet_settled (packet : Packet roles) (member : packet ∈ state.packets)
    (children : All₂ (RecordedTree state) packet.children dictionaries) :
    GeneralNominalSettledSupport.PacketSettled state packet := by
  refine ⟨member,?_⟩
  have all : ∀ sites payloads, All₂ (RecordedTree state) sites payloads →
      ∀ child ∈ sites, Discharged state child := by
    intro sites payloads trees
    induction trees with
    | nil => intro child member; cases member
    | cons tree trees ih =>
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact discharged tree
      · exact ih child member
  exact all _ _ children

theorem current_evidence {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (tree : RecordedTree state.current occurrence payload)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model occurrence payload := by
  induction tree using RecordedTree.rec
    (motive_2 := fun sites payloads _ => All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) sites payloads) with
  | node packet member dictionaries children ih =>
    exact GeneralDictionarySharedRecordedEvidence.current_evidence formed packet member
      (growth packet member) model valid dictionaries ih
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

theorem terminal_tree : RecordedTree GeneralDictionarySharedTerminalInstallation.after.current
    GeneralNominalSupportSiblings.kidC (.node GeneralNominalSupportSiblings.c.id []) := by
  apply RecordedTree.node GeneralNominalDownstreamSiblingFixture.containerPacket
  · exact List.mem_cons_self
  · rw [GeneralNominalBudgetContainer.children]
    exact .nil

theorem terminal_discharged : Discharged GeneralDictionarySharedTerminalInstallation.after.current
    GeneralNominalSupportSiblings.kidC := discharged terminal_tree

theorem terminal_packet_settled : GeneralNominalSettledSupport.PacketSettled
    GeneralDictionarySharedTerminalInstallation.after.current GeneralNominalDownstreamSiblingFixture.containerPacket := by
  apply packet_settled _ List.mem_cons_self (dictionaries := [])
  rw [GeneralNominalBudgetContainer.children]
  exact .nil

/-- The concrete local Shared successor has both the structural certificate and
nonvacuous current semantic evidence. No Shared initial-prefix claim is made. -/
theorem terminal_certificate_and_evidence :
    RecordedTree GeneralDictionarySharedTerminalInstallation.after.current
      GeneralNominalSupportSiblings.kidC (.node GeneralNominalSupportSiblings.c.id []) ∧
    (∃ model, Models GeneralDictionarySharedTerminalInstallation.after.current model) ∧
    ∀ model, Models GeneralDictionarySharedTerminalInstallation.after.current model →
      GeneralDictionaryRecursiveEvidence.Evidence GeneralNominalSupportSiblings.reg
        GeneralDictionarySharedTerminalInstallation.after.current.context model
        GeneralNominalSupportSiblings.kidC (.node GeneralNominalSupportSiblings.c.id []) :=
  ⟨terminal_tree,GeneralDictionarySharedTerminalInstallation.inhabited,
    GeneralDictionarySharedTerminalInstallation.current_dictionary⟩
end Yulang.GeneralDictionarySharedRecordedTree
