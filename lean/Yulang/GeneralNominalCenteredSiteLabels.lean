import Yulang.GeneralNominalCenteredIdentityJournal
import Yulang.GeneralNominalCenteredProgress

/-! Child-label allocation preserves every already registered input forest,
including occurrences whose endpoint demand differs from an older use. -/
namespace Yulang.GeneralNominalCenteredSiteLabels
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCanonicalHoleJournal GeneralNominalCanonicalPacketTransport
open GeneralNominalIdentityJournal GeneralNominalPatersonLineage
open GeneralNominalCompatibleJournalExtension

variable {roles : Roles.RoleDecls} {root : Occurrence roles}

theorem lineage_used (lineage : Lineage registry seed root packets depth occurrence) :
    Used root packets occurrence.identity := by
  cases lineage with
  | root => exact Or.inl rfl
  | child packet member sameRegistry sameSeed visible parent childMem =>
    obtain ⟨clause,present,signature,rfl⟩ := emitted_clause packet _ childMem
    exact Or.inr ⟨packet,member,Or.inr ⟨clause,present,signature,rfl⟩⟩

theorem site_used (path : B4Target.Steps (Step registry root) (initial context root) state)
    (member : site ∈ state.sites) : Used root state.erased.current.packets site.occurrence.identity := by
  obtain ⟨raw,present,same⟩ := GeneralNominalCenteredProgress.sites_correspond path site member
  obtain ⟨depth,lineage⟩ := GeneralNominalCenteredTrace.sites_lineage path raw present
  exact same ▸ lineage_used lineage

theorem new_packet_extension (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (journal : Journal context root state.erased inventory) (identity : IdentityLabels journal.labels)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current packet)
    (matching : packet.declaration.requirements ≠ [] → Matching context journal.labels packet) :
    ∃ labels, IdentityLabels labels ∧ labels root = journal.labels root ∧
      (∀ site ∈ state.sites, labels site.occurrence = journal.labels site.occurrence) ∧
      (∀ prior ∈ state.erased.current.packets, prior.declaration.requirements ≠ [] → Agrees journal.labels labels prior) ∧
      (packet.declaration.requirements ≠ [] → Nonempty (Presentation context labels packet)) := by
  have seed : packet.context.state.seed = context.state.seed := by
    rw [enabled.1.2.1]
    exact (GeneralNominalCenteredTrace.configuration_trace path).1
  obtain ⟨labels,indexed,preserved,same,history,presented⟩ :=
    GeneralNominalIdentityJournal.new_packet_extension_preserving checked journal identity packet enabled.1.2.2.2.1
      (GeneralNominalCenteredTrace.sites_lineage path packet.site enabled.1.2.2.1)
      (fun prior member => ⟨(GeneralNominalCenteredTrace.packet_configuration path prior member).1.trans seed.symm,
        (GeneralNominalCenteredTrace.packet_configuration path prior member).2,
        GeneralNominalCenteredTrace.packets_lineage path prior member⟩) matching
  exact ⟨labels,indexed,same,fun site member => preserved site.occurrence (site_used path member),history,presented⟩

theorem install_journal (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (journal : Journal context root state.erased inventory) (identity : IdentityLabels journal.labels)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (matching : plan.packet.declaration.requirements ≠ [] → Matching context journal.labels plan.packet)
    (support : List (Occurrence roles)) :
    ∃ next : Journal context root (install state plan support).erased inventory, IdentityLabels next.labels ∧
      ∀ site ∈ state.sites, next.labels site.occurrence = journal.labels site.occurrence := by
  obtain ⟨labels,indexed,same,sites,history,presented⟩ := new_packet_extension checked path journal identity enabled matching
  obtain ⟨next,equal⟩ := install_extension journal labels same history plan.packet support presented
  exact ⟨next,equal ▸ indexed,fun site member => equal ▸ sites site member⟩

end Yulang.GeneralNominalCenteredSiteLabels
