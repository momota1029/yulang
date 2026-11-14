import Yulang.GeneralNominalCompatibleJournalExtension

/-! Types of the remaining local source goals. These are propositions to be
constructed from the reachable source invariant, not additional execution
guards or supplied proofs of the universal source construction. -/
namespace Yulang.GeneralNominalSourceProducerHandoff
open GeneralDeclarationPatterns GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalMaterialization GeneralNominalScopedRecipeLabels GeneralNominalReadbackFunctionality
open GeneralNominalLabelledOriginClosure GeneralNominalSupport GeneralNominalSharedSupport
open GeneralNominalSaturationState GeneralNominalHoleElimination GeneralNominalIndexedHoleReadback
open GeneralNominalCanonicalHoleJournal GeneralNominalCanonicalPacketTransport GeneralSourceDictionaries
open GeneralNominalCompatibleJournalExtension

variable {roles : Roles.RoleDecls}
variable {root : Occurrence roles}

def RequestTemplates (context : GeneralNominalCandidates.Context) (requests : List Request) : Prop :=
  NodeTemplates context
    (GeneralNominalSourceLabelVocabulary.collectArgs (requests.map fun request => normalize request.pattern))
    ((generated context.state context.interpretation requests).tests.map Prod.snd)

def RequestCanonical (context : GeneralNominalCandidates.Context) (requests : List Request) : Prop :=
  ∀ entry ∈ (generated context.state context.interpretation requests).tests, TestCanonical entry.2

def TrustedInputs (state : Tracked roles) (facts : List (Fact roles))
    (context : GeneralNominalCandidates.Context) (origins : Nat → Origin)
    (remaining keys : List Nat) (tests : List Test) : Prop :=
  ∀ root ∈ inputOrigins facts,
    ∃ value : Value (GeneralNominalSharedSupport.Models state facts) context origins remaining keys root,
      Vocabulary tests value.term

/-- This is the positive constructor-expansion producer needed at an actual
exposed position. The supplied old leaf and actual K2 safety are consumed by
LabelledExposureElimination.discharge after this local data is constructed. -/
def ConstructorExpansion (state : State roles)
    (identities : Nat → Nat) (inventory : Inventory) (tests : List Test) (actual : Nat) : Prop :=
  ∃ test children,
    Readback (GeneralNominalSaturationState.Models state) (fun name => .source (identities name))
      inventory.holes (.source actual) (.node test children) ∧
    Canonical (.node test children) ∧ Vocabulary tests (.node test children) ∧
    GeneralNominalBackedHoleElimination.Backed state identities actual (.node test children)

/-- Apply this goal only after the necessary global replacements. Agreement
is required on every old nonterminal packet's input and child labels. -/
def NewPacket (journal : Journal context root before inventory) (packet : Packet roles) : Prop :=
  ∃ labels : Occurrence roles → List Pattern,
    labels root = journal.labels root ∧
    (∀ prior ∈ before.current.packets, prior.declaration.requirements ≠ [] → Agrees journal.labels labels prior) ∧
    (packet.declaration.requirements ≠ [] → Nonempty (Presentation context labels packet))

theorem new_packet_installs (journal : Journal context root before inventory)
    (packet : Packet roles) (support : List (Occurrence roles)) (ready : NewPacket journal packet) :
    Nonempty (Journal context root (GeneralNominalSharedSteps.install before packet support) inventory) := by
  obtain ⟨labels,rootSame,history,presented⟩ := ready
  obtain ⟨result,_⟩ := install_extension journal labels rootSame history packet support presented
  exact ⟨result⟩

end Yulang.GeneralNominalSourceProducerHandoff
