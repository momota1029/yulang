import Yulang.GeneralDictionaryRecursiveEvidence
import Yulang.GeneralNominalSaturationInvariants

/-! Committed packets supply branch equations in every final journal model.
The source judgment remains the cycle130 model-indexed judgment. Stability
closes only installable packets; feedback and alias-choice coherence are named
premises below, not consequences asserted for arbitrary stable states. -/
namespace Yulang.GeneralDictionaryCommittedEvidence

open GeneralDeclarations
open GeneralSourceDictionaries (Occurrence)
open GeneralDictionaryReadback (Payload)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState GeneralNominalSaturationSteps
open GeneralNominalRecursiveCandidates (Survivor Prepared)
open CommonRoleOutermostResolver (All₂)

variable {roles : Roles.RoleDecls}

/-- The selected key must agree with previously recorded choices at every alias.
This is a real outstanding invariant, not part of the frozen Stable predicate. -/
def AliasChoiceAgreement (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ prior ∈ state.packets, Alias state root.identity prior.site.occurrence.identity →
    key = prior.declaration.id

/-- A committed current-context source packet is an instance in each state model.
All source guards are retained; no existential model is substituted. -/
theorem committed_instance (state : State roles) (packet : Packet roles)
    (visible : packet.declaration ∈ packet.registry.declarations)
    (role : packet.declaration.role = packet.site.occurrence.demand.role)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (prepared : Prepared packet.registry packet.context packet.site.occurrence packet.declaration packet.checked)
    (committed : Committed state packet)
    (model : Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance packet.registry packet.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  obtain ⟨metadata,_,_,bounds,found,finished,ready,_⟩ := prepared
  have same := Option.some.inj (located.symm.trans found)
  subst bounds
  exact ⟨packet.declaration,visible,packet.checked,rfl,role,packet.bounds,located,
    finished,ready,rfl,metadata,committed.1 model valid⟩

/-- Installing a checked source packet gives its original source instance in
all successor models. The inspection context is explicitly the packet's stored
context; this is not a transport theorem to a regenerated inspection context. -/
theorem installed_instance (state : State roles) (packet : Packet roles)
    (emitted : Emitted packet)
    (visible : packet.declaration ∈ packet.registry.declarations)
    (role : packet.declaration.role = packet.site.occurrence.demand.role)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (prepared : Prepared packet.registry packet.context packet.site.occurrence packet.declaration packet.checked)
    (model : Assignment) (valid : Models (install state packet emitted) model) :
    GeneralDictionaryRecursiveEvidence.Instance packet.registry packet.context model
      packet.site.occurrence packet.declaration.id packet.children :=
  committed_instance _ packet visible role located prepared
    (installed_committed state packet emitted) model valid

/-- Actual recorded edges, not only source emission membership. -/
theorem committed_children (state : State roles) (packet : Packet roles)
    (committed : Committed state packet) (child : Occurrence roles)
    (member : child ∈ packet.children) : Generated state packet.site.occurrence child :=
  .child .root (committed.2 child member)

/-- Explicitly isolate what stability does provide once installation is enabled. -/
theorem stable_installable_committed (registry : Registry) (state : State roles)
    (packet : Packet roles) (stable : Stable registry state packet.site.occurrence)
    (enabled : Installable registry state packet) : Committed state packet :=
  (stable packet.site.occurrence .root).2.1 packet rfl enabled

/-- Registration and merge closure come from stability. Feedback supplies joint
consistency; alias agreement supplies the other installation guard. -/
theorem stable_selected_packet (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state root)
    (complete : ContextComplete state)
    (agreement : AliasChoiceAgreement state root key)
    (selected : GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles)
      registry state.context root (.selected key children)) :
    ∃ packet : Packet roles, packet.registry = registry ∧ packet.context = state.context ∧
      packet.site.occurrence = root ∧ packet.declaration.id = key ∧ packet.children = children ∧
      Installable registry state packet ∧ Committed state packet := by
  have survivor : Survivor registry state.context root key children := by
    cases selected with | selected _ unique => exact unique.1
  obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,emitted⟩ := survivor
  obtain ⟨site,member,same⟩ := (stable root .root).1 prepared.2.1
  let packet : Packet roles := ⟨registry,state.context,site,declaration,checked,bounds⟩
  have exactChildren : packet.children = children := by
    change GeneralNominalAllocation.children state.context.state registry site.occurrence declaration checked _ = children
    rw [same]
    exact emitted.symm
  have enabled : Installable registry state packet := by
    refine ⟨rfl,rfl,member,visible,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [packet,same] using role
    · simpa only [packet,same] using located
    · simpa only [packet,same] using prepared
    · change GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles)
        registry state.context site.occurrence (.selected declaration.id packet.children)
      rw [same,identity,exactChildren]
      exact selected
    · intro prior present alias
      apply identity.trans
      apply agreement prior present
      simpa only [packet,same] using alias
    · intro other present inputs
      exact (stable root .root).2.2.1 site member same other present inputs
    · obtain ⟨_,_,_,other,found,_,_,model,branch⟩ := prepared
      have equal := Option.some.inj (located.symm.trans found)
      subst other
      refine ⟨model,complete model
        (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ branch).1,?_⟩
      simpa only [Packet.Holds,packet,same] using branch
  exact ⟨packet,rfl,rfl,same,identity,exactChildren,enabled,
    (stable root .root).2.1 packet same enabled⟩

/-- Universal final-model source instances, conditional on the two explicit
journal invariants which the current Stable definition does not supply. -/
theorem stable_selected_instance (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state root) (complete : ContextComplete state)
    (agreement : AliasChoiceAgreement state root key)
    (selected : GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles)
      registry state.context root (.selected key children)) :
    (∀ model, Models state model → GeneralDictionaryRecursiveEvidence.Instance
      registry state.context model root key children) ∧
      ∀ child ∈ children, Generated state root child := by
  obtain ⟨packet,registrySame,contextSame,rootSame,keySame,childrenSame,enabled,committed⟩ :=
    stable_selected_packet registry state root key children stable complete agreement selected
  constructor
  · intro model valid
    have source := committed_instance state packet
      (by simpa only [registrySame] using enabled.2.2.2.1)
      enabled.2.2.2.2.1 enabled.2.2.2.2.2.1 enabled.2.2.2.2.2.2.1 committed model valid
    simpa only [registrySame,contextSame,rootSame,keySame,childrenSame] using source
  · intro child member
    have source := committed_children state packet committed child (by simpa only [childrenSame] using member)
    simpa only [rootSame] using source

/-- Every child and the parent are interpreted in the same arbitrary final model. -/
theorem stable_selected_evidence (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state root) (complete : ContextComplete state)
    (agreement : AliasChoiceAgreement state root key)
    (selected : GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles)
      registry state.context root (.selected key children))
    (model : Assignment) (valid : Models state model) (dictionaries : List Payload)
    (given : All₂ (GeneralDictionaryRecursiveEvidence.Evidence registry state.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root (.node key dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry state.context model root key children dictionaries
    ((stable_selected_instance registry state root key children stable complete agreement selected).1 model valid) given

end Yulang.GeneralDictionaryCommittedEvidence
