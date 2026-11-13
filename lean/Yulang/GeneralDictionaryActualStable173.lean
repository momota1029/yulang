import Yulang.GeneralNominalActualBoundary
import Yulang.GeneralDictionaryCommittedEvidence

/-! I-28: actual Stable closes actually guarded, installable packets.
The PacketGuard premise includes shared generation and actual-position checks;
it is not inferred from the inherited Local classification. -/
namespace Yulang.GeneralDictionaryActualStable173
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralDictionaryRecursiveEvidence
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

theorem stable_committed (packet : Packet roles) (support : List (Occurrence roles))
    (stable : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : PacketGuard state packet support) :
    GeneralNominalFeedbackSteps.Committed state.current packet := by
  classical
  apply Classical.byContradiction
  intro novel
  exact stable packet.site.occurrence .root _ (.install packet support enabled novel guard)

theorem stable_site (root : Occurrence roles)
    (stable : GeneralNominalActualBoundary.Stable registry state root)
    (linked : GeneralNominalState.Linked state.current.context.state root.demand) :
    ∃ site ∈ state.current.sites, site.occurrence = root := by
  classical
  apply Classical.byContradiction
  intro missing
  have absent : ∀ site ∈ state.current.sites, site.occurrence ≠ root := by
    intro site member same
    exact missing ⟨site,member,same⟩
  exact stable root .root _ (.administrative root _ (.enqueue root linked absent))

theorem uncommitted_not_guarded (packet : Packet roles) (support : List (Occurrence roles))
    (stable : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet) :
    ¬ PacketGuard state packet support :=
  fun guard => novel (stable_committed packet support stable enabled guard)

theorem stable_instance (packet : Packet roles) (support : List (Occurrence roles))
    (stable : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : PacketGuard state packet support) (model : Assignment)
    (valid : Models state.current model) :
    Instance registry state.current.context model packet.site.occurrence packet.declaration.id packet.children := by
  have given := GeneralDictionaryCommittedEvidence.committed_instance state.current packet
    (by simpa only [enabled.1.1] using enabled.1.2.2.2.1)
    enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 enabled.1.2.2.2.2.2.2.1
    (stable_committed packet support stable enabled guard) model valid
  simpa only [enabled.1.1,enabled.1.2.1] using given

theorem stable_children (packet : Packet roles) (support : List (Occurrence roles))
    (stable : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : PacketGuard state packet support) :
    ∀ child ∈ packet.children, Generated state.current packet.site.occurrence child :=
  GeneralDictionaryCommittedEvidence.committed_children _ packet
    (stable_committed packet support stable enabled guard)

theorem stable_evidence (packet : Packet roles) (support : List (Occurrence roles))
    (stable : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : PacketGuard state packet support) (model : Assignment)
    (valid : Models state.current model) (dictionaries : List Payload)
    (children : All₂ (Evidence registry state.current.context model) packet.children dictionaries) :
    Evidence registry state.current.context model packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  evidence_node _ _ _ _ _ _ _ (stable_instance packet support stable enabled guard model valid) children

/-- No unconditional Local-to-guard claim: this primitive residual contains
neither Evidence nor Committed nor a B4 conclusion. -/
def SelectedPackets (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (GeneralNominalActualBoundary.boundary roles).Checked registry → ∀ state root,
    B4TargetV5.Reachable (GeneralNominalActualBoundary.boundary roles) registry root state →
    ∀ focus key children, (focus = root ∨ Generated state.current root focus) →
    GeneralNominalActualBoundary.Stable registry state focus →
    GeneralNominalActualBoundary.Local registry state focus (.selected key children) →
    ∃ packet : Packet roles, ∃ support : List (Occurrence roles),
      packet.site.occurrence = focus ∧ packet.declaration.id = key ∧ packet.children = children ∧
      GeneralNominalFeedbackSteps.Installable registry state.current packet ∧ PacketGuard state packet support

theorem evidenceNode (packets : SelectedPackets roles) :
    B4SkeletonV5.EvidenceNode (GeneralNominalActualBoundary.boundary roles) := by
  intro registry checked state root reachable model valid focus key children dictionaries reached stable _ safe unique given
  have selected := (GeneralNominalActualBoundary.local_correspondence registry state focus _).mp
    (B4TargetV3.Local.selected safe unique)
  obtain ⟨packet,support,same,keySame,childrenSame,enabled,guard⟩ :=
    packets registry checked state root reachable focus key children reached stable selected
  have stablePacket : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence := same.symm ▸ stable
  have instanceRule := stable_instance packet support stablePacket enabled guard model valid
  rw [same,keySame,childrenSame] at instanceRule
  exact evidence_node _ _ _ _ _ _ _ instanceRule given

theorem generatedChildren (packets : SelectedPackets roles) :
    B4SkeletonV5.GeneratedChildren (GeneralNominalActualBoundary.boundary roles) := by
  intro registry checked state root focus key children reachable reached stable safe unique child member
  have selected := (GeneralNominalActualBoundary.local_correspondence registry state focus _).mp
    (B4TargetV3.Local.selected safe unique)
  obtain ⟨packet,support,same,keySame,childrenSame,enabled,guard⟩ :=
    packets registry checked state root reachable focus key children reached stable selected
  have stablePacket : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence := same.symm ▸ stable
  have path := stable_children packet support stablePacket enabled guard child (childrenSame.symm ▸ member)
  rw [same] at path
  rcases reached with rfl | generated
  · exact path
  · exact generated_trans generated path

end Yulang.GeneralDictionaryActualStable173
