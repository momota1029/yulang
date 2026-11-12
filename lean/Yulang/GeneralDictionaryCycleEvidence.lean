import Yulang.GeneralDictionaryCommittedEvidence
import Yulang.GeneralNominalCycleBoundary
import Yulang.B4SkeletonV4

/-! Source dictionary evidence on Astra's cycle boundary. Joint applicability
supplies a single journal-compatible branch witness and recorded-choice
agreement. It does not follow from the unchanged local Survivor interface.
No context-completeness premise and no strengthened Stable are introduced. -/
namespace Yulang.GeneralDictionaryCycleEvidence

open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalCycleSteps
open GeneralNominalJointCandidates (Joint)
open GeneralDictionaryReadback (Payload)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls}

/-- Exactly Astra's cycle local and transition fields, plus source evidence. -/
def boundary (roles : Roles.RoleDecls) :
    B4Target.SourceBoundary (GeneralNominalSaturationBoundary.vocabulary roles) :=
  GeneralNominalLocalBoundary.complete (GeneralNominalCycleBoundary.localFields roles)
    { Step := Step
      Stable := Stable
      Generated := fun _ state => Generated state
      Evidence := fun registry state => GeneralDictionaryRecursiveEvidence.Evidence registry state.context }

/-- Joint's root branch is sufficient to construct the actual selected packet.
The common witness is in Models state, rather than merely the ordinary context. -/
theorem stable_joint_packet (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state root)
    (selected : GeneralNominalCycleK2.Local registry state.context root (.selected key children))
    (joint : Joint registry state root key) :
    ∃ packet : Packet roles, packet.registry = registry ∧ packet.context = state.context ∧
      packet.site.occurrence = root ∧ packet.declaration.id = key ∧ packet.children = children ∧
      Installable registry state packet ∧ Committed state packet := by
  obtain ⟨model,valid,branch,_⟩ := joint.2
  obtain ⟨declaration,visible,checked,identity,role,prepared,bounds,located,holds⟩ := branch
  obtain ⟨site,member,same⟩ := (stable root .root).1 prepared.2.1
  let packet : Packet roles := ⟨registry,state.context,site,declaration,checked,bounds⟩
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.context root key packet.children := by
    refine ⟨?_,declaration,visible,checked,identity,role,bounds,located,prepared,?_⟩
    · cases selected with | selected safe _ => exact safe.1
    · change GeneralNominalAllocation.children state.context.state registry site.occurrence declaration checked _ = _
      rw [same]
      rfl
  have exactChildren : packet.children = children := by
    cases selected with | selected _ unique => exact (unique.2 key packet.children survivor).2
  have enabled : Installable registry state packet := by
    refine ⟨rfl,rfl,member,visible,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [packet,same] using role
    · simpa only [packet,same] using located
    · simpa only [packet,same] using prepared
    · change GeneralNominalCycleK2.Local registry state.context site.occurrence (.selected declaration.id packet.children)
      rw [same,identity,exactChildren]
      exact selected
    · intro prior present alias
      apply identity.trans
      apply Eq.symm
      apply joint.1 prior present
      simpa only [packet,same] using alias
    · intro other present inputs
      exact (stable root .root).2.2.1 site member same other present inputs
    · refine ⟨model,valid,?_⟩
      simpa only [Packet.Holds,packet,same] using holds
    · simpa only [packet,same,identity] using joint
  exact ⟨packet,rfl,rfl,same,identity,exactChildren,enabled,
    (stable root .root).2.1 packet same enabled⟩

/-- Source instances and journal-generated children in every final model. -/
theorem stable_joint_instance (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state root)
    (selected : GeneralNominalCycleK2.Local registry state.context root (.selected key children))
    (joint : Joint registry state root key) :
    (∀ model, Models state model → GeneralDictionaryRecursiveEvidence.Instance
      registry state.context model root key children) ∧
      ∀ child ∈ children, Generated state root child := by
  obtain ⟨packet,registrySame,contextSame,rootSame,keySame,childrenSame,enabled,committed⟩ :=
    stable_joint_packet registry state root key children stable selected joint
  constructor
  · intro model valid
    have source := GeneralDictionaryCommittedEvidence.committed_instance state packet
      (by simpa only [registrySame] using enabled.2.2.2.1)
      enabled.2.2.2.2.1 enabled.2.2.2.2.2.1 enabled.2.2.2.2.2.2.1 committed model valid
    simpa only [registrySame,contextSame,rootSame,keySame,childrenSame] using source
  · intro child member
    have source := GeneralDictionaryCommittedEvidence.committed_children state packet committed child
      (by simpa only [childrenSame] using member)
    simpa only [rootSame] using source

/-- The unchanged model-indexed source Evidence, not a proxy predicate. -/
theorem stable_joint_evidence (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state root)
    (selected : GeneralNominalCycleK2.Local registry state.context root (.selected key children))
    (joint : Joint registry state root key)
    (model : Assignment) (valid : Models state model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root (.node key dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry state.context model root key children dictionaries
    ((stable_joint_instance registry state root key children stable selected joint).1 model valid) given

/-- The remaining joint-classification obligation is explicit and not built
into Stable or Local. It is not asserted for all raw journal states. -/
def SelectedJoint (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ (state : State roles) (root : Occurrence roles) key children,
    Stable registry state root →
    GeneralNominalCycleK2.Local registry state.context root (.selected key children) →
    Joint registry state root key

theorem evidenceNode_of_selected_joint (roles : Roles.RoleDecls)
    (joint : SelectedJoint roles) : B4SkeletonV4.EvidenceNode (boundary roles) := by
  intro registry checked state model valid root key children dictionaries stable _ safe unique given
  have selected := (GeneralNominalCycleBoundary.local_projection registry state root _).mp
    (GeneralNominalLocalBoundary.Local.selected safe unique)
  exact stable_joint_evidence registry state root key children stable selected
    (joint registry checked state root key children stable selected) model valid dictionaries given

theorem generatedChildren_of_selected_joint (roles : Roles.RoleDecls)
    (joint : SelectedJoint roles) : B4SkeletonV4.GeneratedChildren (boundary roles) := by
  apply B4SkeletonV4.generatedChildren_of_direct_transitive
  · intro registry checked state root key children stable safe unique child member
    have selected := (GeneralNominalCycleBoundary.local_projection registry state root _).mp
      (GeneralNominalLocalBoundary.Local.selected safe unique)
    exact (stable_joint_instance registry state root key children stable selected
      (joint registry checked state root key children stable selected)).2 child member
  · intro _ _ _ _ _ _ first last
    exact generated_trans first last

theorem closure (roles : Roles.RoleDecls) :
    ∀ registry, (boundary roles).Checked registry → ∀ state root,
      (∀ next, ¬ (boundary roles).Step registry root state next) →
      (boundary roles).Stable registry state root ∧
        ∀ child, (boundary roles).Generated registry state root child →
          (boundary roles).Stable registry state child := by
  intro registry _ state root halted
  exact halted_closure halted

theorem stepModels (roles : Roles.RoleDecls) :
    ∀ registry, (boundary roles).Checked registry → ∀ root before after,
      (boundary roles).Step registry root before after →
      ∀ model, (boundary roles).Models after model → (boundary roles).Models before model := by
  intro registry _ root before after update model valid
  exact step_models update model valid

theorem dictionaryRefl (roles : Roles.RoleDecls) :
    ∀ dictionary, (boundary roles).DictionaryEquivalent dictionary dictionary :=
  GeneralDictionaryPayloadOrder.equivalent_refl

/-- K2 rejection excludes the selected local frontier used to assemble a
dictionary. Raw source Evidence itself deliberately has no K2 premise. -/
theorem rootK2_no_selected (registry : Registry) (state : State roles)
    (root : Occurrence roles)
    (cycle : GeneralNominalCycleK2.RootK2 state.context.state root.demand)
    (key : Nat) (children : List (Occurrence roles)) :
    ¬ GeneralNominalLocalBoundary.Local (GeneralNominalCycleBoundary.localFields roles)
      registry state root (.selected key children) := by
  intro selected
  exact (GeneralNominalCycleK2.selected_not_K2
    ((GeneralNominalCycleBoundary.local_projection registry state root _).mp selected)).1 cycle

theorem candidateK2_no_selected (registry : Registry) (state : State roles)
    (root : Occurrence roles)
    (cycle : GeneralNominalCycleK2.CandidateK2 registry state.context root)
    (key : Nat) (children : List (Occurrence roles)) :
    ¬ GeneralNominalLocalBoundary.Local (GeneralNominalCycleBoundary.localFields roles)
      registry state root (.selected key children) := by
  intro selected
  exact (GeneralNominalCycleK2.selected_not_K2
    ((GeneralNominalCycleBoundary.local_projection registry state root _).mp selected)).2 cycle

end Yulang.GeneralDictionaryCycleEvidence
