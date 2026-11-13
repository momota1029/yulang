import Yulang.GeneralNominalJournalSimulation

/-! New child occurrences may receive new labels while every historical
packet retains its simultaneous presentation. This separates label extension
from genuine global hole substitution. No freshness assertion is assumed
merely from allocation of a numeric identity. -/
namespace Yulang.GeneralNominalCompatibleJournalExtension
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalCanonicalPacketTransport GeneralNominalCanonicalHoleJournal
open GeneralNominalHoleElimination GeneralNominalLabelledOriginClosure

variable {roles : Roles.RoleDecls}

def Agrees (first last : Occurrence roles → List Pattern) (packet : Packet roles) : Prop :=
  last packet.site.occurrence = first packet.site.occurrence ∧
  ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
    last (GeneralNominalFeedbackSites.clauseChild packet clause signature) =
      first (GeneralNominalFeedbackSites.clauseChild packet clause signature)

def relabel_presentation (presented : Presentation context first packet) (agrees : Agrees first last packet) :
    Presentation context last packet where
  capture := presented.capture
  trees := presented.trees
  captureLabels := presented.captureLabels
  coveredHead := presented.coveredHead
  head := agrees.1 ▸ presented.head
  children := fun clause member signature => (agrees.2 clause member signature).trans (presented.children clause member signature)

def relabel_journal (journal : Journal context root state inventory)
    (labels : Occurrence roles → List Pattern) (rootSame : labels root = journal.labels root)
    (history : ∀ packet ∈ state.current.packets, packet.declaration.requirements ≠ [] → Agrees journal.labels labels packet) :
    Journal context root state inventory where
  labels := labels
  member := rootSame ▸ journal.member
  rootLabels := rootSame ▸ journal.rootLabels
  history := by
    intro packet member nonempty
    obtain ⟨presented⟩ := journal.history packet member nonempty
    exact ⟨relabel_presentation presented (history packet member nonempty)⟩

theorem install_extension (journal : Journal context root before inventory)
    (labels : Occurrence roles → List Pattern) (rootSame : labels root = journal.labels root)
    (history : ∀ prior ∈ before.current.packets, prior.declaration.requirements ≠ [] → Agrees journal.labels labels prior)
    (packet : Packet roles) (support : List (Occurrence roles))
    (presented : packet.declaration.requirements ≠ [] → Nonempty (Presentation context labels packet)) :
    ∃ result : Journal context root (GeneralNominalSharedSteps.install before packet support) inventory,
      result.labels = labels :=
  ⟨(relabel_journal journal labels rootSame history).install packet support presented,rfl⟩

theorem eliminating_extension (journal : Journal context root before inventory)
    (replacement : Value models context origins (inventory.holes.erase hole) keys (origins hole))
    (present : hole ∈ inventory.holes)
    (labels : Occurrence roles → List Pattern)
    (rootSame : labels root = substituteLabels journal.labels (patternReplacement hole replacement.pattern) root)
    (history : ∀ prior ∈ before.current.packets, prior.declaration.requirements ≠ [] →
      Agrees (substituteLabels journal.labels (patternReplacement hole replacement.pattern)) labels prior)
    (packet : Packet roles) (support : List (Occurrence roles))
    (presented : packet.declaration.requirements ≠ [] → Nonempty (Presentation context labels packet)) :
    ∃ extra, Trace (GeneralNominalSourceLabelVocabulary.tests keys) (fun _ => extra) inventory
      (eliminate inventory hole (GeneralNominalPatternInventory.encode replacement.pattern) extra) 1 ∧
      ∃ result : Journal context root (GeneralNominalSharedSteps.install before packet support)
        (eliminate inventory hole (GeneralNominalPatternInventory.encode replacement.pattern) extra), result.labels = labels := by
  obtain ⟨extra,trace⟩ := GeneralNominalSourceLabelVocabulary.replacement_trace inventory present replacement.allowed
  exact ⟨extra,trace,install_extension (journal.replace replacement.labelled.1 hole extra) labels rootSame history packet support presented⟩

end Yulang.GeneralNominalCompatibleJournalExtension
