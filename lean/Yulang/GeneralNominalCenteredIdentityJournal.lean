import Yulang.GeneralNominalCenteredTrace

/-! Identity-indexed journals initialize with unknown source holes and extend
along full centered traces. Historical compatibility is constructed from the
allocation genealogy; only new head matching remains a producer premise. -/
namespace Yulang.GeneralNominalCenteredIdentityJournal
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination
open GeneralNominalIdentityJournal GeneralNominalCenteredTrace
open GeneralNominalSourceProducerHandoff GeneralNominalCompatibleJournalExtension
open GeneralNominalCanonicalPacketTransport

variable {roles : Roles.RoleDecls} {root : Occurrence roles}

theorem initial_journal
    (source : GeneralNominalSourceFormation.InitialSource registry context root) (keys : List Nat) :
    ∃ inventory : Inventory,
      inventory.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length ∧
      Valid (GeneralNominalSourceLabelVocabulary.tests keys) inventory ∧
      ∃ journal : Journal context root (initial context root).erased inventory,
        IdentityLabels journal.labels ∧
        journal.labels root = GeneralNominalSourceInitialization.rootPatterns context root := by
  obtain ⟨inventory,holes,valid,journal,same⟩ := GeneralNominalSourceInitialization.initial_journal source keys
  exact ⟨inventory,holes,valid,{
    labels := fun _ => journal.labels root
    member := journal.member
    rootLabels := journal.rootLabels
    history := by intro packet member; cases member },fun _ _ _ => rfl,same⟩

theorem identity_transform (operations : List GeneralNominalCaptureRefinement.Operation)
    (identity : IdentityLabels labels) :
    IdentityLabels (GeneralNominalCaptureFamilies.transformLabels operations labels) := by
  induction operations generalizing labels with
  | nil => exact identity
  | cons op rest ih => exact ih (identity_substitute identity _)

theorem refinement_journal
    (refinement : GeneralNominalCaptureRefinement.Refinement models context identities keys tests before after operations)
    (journal : Journal context root state before) (identity : IdentityLabels journal.labels) :
    ∃ next : Journal context root state after, IdentityLabels next.labels ∧
      next.labels = GeneralNominalCaptureFamilies.transformLabels operations journal.labels := by
  obtain ⟨next,same⟩ := GeneralNominalCaptureFamilies.journal refinement journal
  exact ⟨next,same ▸ identity_transform operations identity,same⟩

theorem new_packet_extension (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (journal : Journal context root state.erased inventory) (identity : IdentityLabels journal.labels)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current packet)
    (matching : packet.declaration.requirements ≠ [] → Matching context journal.labels packet) :
    ∃ labels, IdentityLabels labels ∧ labels root = journal.labels root ∧
      (∀ prior ∈ state.erased.current.packets, prior.declaration.requirements ≠ [] → Agrees journal.labels labels prior) ∧
      (packet.declaration.requirements ≠ [] → Nonempty (Presentation context labels packet)) := by
  have seed : packet.context.state.seed = context.state.seed := by
    rw [enabled.1.2.1]
    exact (configuration_trace path).1
  exact GeneralNominalIdentityJournal.new_packet_extension checked journal identity packet enabled.1.2.2.2.1
    (sites_lineage path packet.site enabled.1.2.2.1)
    (fun prior member => ⟨(packet_configuration path prior member).1.trans seed.symm,
      (packet_configuration path prior member).2,packets_lineage path prior member⟩) matching

theorem new_packet (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (journal : Journal context root state.erased inventory) (identity : IdentityLabels journal.labels)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current packet)
    (matching : packet.declaration.requirements ≠ [] → Matching context journal.labels packet) :
    NewPacket journal packet := by
  obtain ⟨labels,_,same,history,presented⟩ := new_packet_extension checked path journal identity enabled matching
  exact ⟨labels,same,history,presented⟩

theorem install_journal (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (journal : Journal context root state.erased inventory) (identity : IdentityLabels journal.labels)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (matching : plan.packet.declaration.requirements ≠ [] → Matching context journal.labels plan.packet)
    (support : List (Occurrence roles)) :
    ∃ next : Journal context root (install state plan support).erased inventory, IdentityLabels next.labels := by
  obtain ⟨labels,indexed,same,history,presented⟩ := new_packet_extension checked path journal identity enabled matching
  obtain ⟨next,equal⟩ := install_extension journal labels same history plan.packet support presented
  exact ⟨next,equal ▸ indexed⟩

end Yulang.GeneralNominalCenteredIdentityJournal
