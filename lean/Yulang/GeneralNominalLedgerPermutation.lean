import Yulang.GeneralNominalJournalPermutation
import Yulang.GeneralNominalMetadataInspection

/-! One packet correspondence is used for the journal and every input/output
fact. Functionality retains the exact identity needed by settled promotion. -/
namespace Yulang.GeneralNominalLedgerPermutation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalJournalPermutation (PacketPair)

abbrev All₂ := @CommonRoleOutermostResolver.All₂

def Reads (packet : Packet roles) (observation : GeneralCanonicalObservations.Observation) : Prop :=
  ∃ slot ∈ readsMany packet.context.state
    (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration) packet.bounds,
    ∃ test, Head packet.context.state (packet.context.state.base.source slot) test observation

structure PacketObservation (first last : Packet roles) : Prop extends PacketPair first last where
  reads : ∀ observation, Reads first observation ↔ Reads last observation
  named : GeneralNominalPacketSupport.namedSchema first = GeneralNominalPacketSupport.namedSchema last
  input : GeneralNominalPacketSupport.inputSchema first = GeneralNominalPacketSupport.inputSchema last
  outputNames : first.declaration.outputNames = last.declaration.outputNames
  capture : GeneralNominalPacketSupport.capture first = GeneralNominalPacketSupport.capture last
  captured : ∀ models name origin,
    GeneralNominalSharedCaptures.Captured first models name origin ↔ GeneralNominalSharedCaptures.Captured last models name origin

namespace PacketObservation

theorem refl (packet : Packet roles) : PacketObservation packet packet :=
  ⟨PacketPair.refl packet,fun _ => Iff.rfl,rfl,rfl,rfl,rfl,fun _ _ _ => Iff.rfl⟩

theorem symm (pair : PacketObservation first last) : PacketObservation last first :=
  ⟨pair.toPacketPair.symm,fun _ => (pair.reads _).symm,pair.named.symm,pair.input.symm,pair.outputNames.symm,pair.capture.symm,
    fun _ _ _ => (pair.captured _ _ _).symm⟩

theorem rebase (packet : Packet roles) (order : GeneralRegistryReordering.Reorders packet.registry registry)
    (pair : GeneralRegistryReordering.DeclarationReorders packet.declaration declaration)
    (roleEq : packet.registry.roles = roles) :
    PacketObservation packet (GeneralNominalPacketReordering.rebase packet order pair) := by
  refine ⟨PacketPair.rebase packet order pair roleEq,?_,
    (GeneralNominalPacketReordering.named_schema order pair roleEq).symm,
    (GeneralNominalPacketReordering.input_schema order pair).symm,?_,
    (GeneralNominalPacketReordering.capture order pair).symm,?_⟩
  · intro observation
    simp only [Reads,GeneralNominalPacketReordering.rebase,GeneralNominalInspection.queries,
      Declaration.normalHead,pair.head]
    rfl
  · simp only [GeneralNominalPacketReordering.rebase,Declaration.outputNames,pair.outputBinders]
  · intro models name origin
    simp only [GeneralNominalSharedCaptures.Captured,GeneralNominalSharedCaptures.inheritedReport,
      GeneralNominalPacketReordering.rebase,GeneralNominalInspection.queries,Declaration.normalHead,pair.head]
    rfl
end PacketObservation

inductive FactPair (relation : Packet roles → Packet roles → Prop) : Fact roles → Fact roles → Prop
  | inputs : relation first last → FactPair relation (.inputs first support) (.inputs last support)
  | outputs : relation first last → FactPair relation (.outputs first support) (.outputs last support)
  | merge : FactPair relation (.merge first last support) (.merge first last support)

theorem all₂_left {α β : Type} {relation : α → β → Prop} {first : List α} {last : List β} {value : α}
    (pairs : All₂ relation first last) (member : value ∈ first) : ∃ other ∈ last, relation value other := by
  induction pairs with
  | nil => cases member
  | cons pair rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,List.mem_cons_self ..,pair⟩
    · obtain ⟨other,found,pair⟩ := ih member
      exact ⟨other,List.mem_cons_of_mem _ found,pair⟩

theorem all₂_right {α β : Type} {relation : α → β → Prop} {first : List α} {last : List β} {value : β}
    (pairs : All₂ relation first last) (member : value ∈ last) : ∃ other ∈ first, relation other value := by
  induction pairs with
  | nil => cases member
  | cons pair rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,List.mem_cons_self ..,pair⟩
    · obtain ⟨other,found,pair⟩ := ih member
      exact ⟨other,List.mem_cons_of_mem _ found,pair⟩

structure Coherent (relation : Packet roles → Packet roles → Prop) : Prop where
  left : ∀ {packet one two}, relation packet one → relation packet two → one = two
  right : ∀ {packet one two}, relation one packet → relation two packet → one = two
  sound : ∀ {first last}, relation first last → PacketObservation first last

namespace Coherent
variable {roles : Roles.RoleDecls} {relation : Packet roles → Packet roles → Prop}

theorem fact_left (coherent : Coherent relation) (one : FactPair relation first middle)
    (two : FactPair relation first last) : middle = last := by
  cases one <;> cases two
  · exact congrArg (fun packet => Fact.inputs packet _) (coherent.left ‹_› ‹_›)
  · exact congrArg (fun packet => Fact.outputs packet _) (coherent.left ‹_› ‹_›)
  · rfl

theorem fact_right (coherent : Coherent relation) (one : FactPair relation middle last)
    (two : FactPair relation first last) : middle = first := by
  cases one <;> cases two
  · exact congrArg (fun packet => Fact.inputs packet _) (coherent.right ‹_› ‹_›)
  · exact congrArg (fun packet => Fact.outputs packet _) (coherent.right ‹_› ‹_›)
  · rfl

theorem holds (coherent : Coherent relation) (pair : FactPair relation first last) (model) :
    first.Holds model ↔ last.Holds model := by
  cases pair with
  | inputs pair => exact (coherent.sound pair).toPacketPair.inputs model
  | outputs pair => exact (coherent.sound pair).toPacketPair.outputs model
  | merge => exact Iff.rfl

theorem dependencies (coherent : Coherent relation) (pair : FactPair relation first last) :
    first.dependencies = last.dependencies := by
  cases pair with
  | inputs => rfl
  | outputs pair => exact congrArg (fun site => site.occurrence :: _) (coherent.sound pair).site
  | merge => rfl

theorem fact_members (coherent : Coherent relation) (facts : All₂ (FactPair relation) first last)
    (pair : FactPair relation one two) : one ∈ first ↔ two ∈ last := by
  constructor
  · intro member
    obtain ⟨other,found,actual⟩ := all₂_left facts member
    exact coherent.fact_left actual pair ▸ found
  · intro member
    obtain ⟨other,found,actual⟩ := all₂_right facts member
    exact coherent.fact_right actual pair ▸ found

theorem facts_models (coherent : Coherent relation) (facts : All₂ (FactPair relation) first last) (model) :
    (∀ fact ∈ first, fact.Holds model) ↔ ∀ fact ∈ last, fact.Holds model := by
  constructor
  · intro valid fact member
    obtain ⟨other,found,pair⟩ := all₂_right facts member
    exact (coherent.holds pair model).mp (valid other found)
  · intro valid fact member
    obtain ⟨other,found,pair⟩ := all₂_left facts member
    exact (coherent.holds pair model).mpr (valid other found)

theorem symm (coherent : Coherent relation) : Coherent (fun last first => relation first last) :=
  ⟨coherent.right,coherent.left,fun pair => (coherent.sound pair).symm⟩

end Coherent

structure Related (relation : Packet roles → Packet roles → Prop) (first last : Tracked roles) : Prop where
  coherent : Coherent relation
  source : first.source = last.source
  current : GeneralNominalJournalPermutation.Related first.current last.current
  recorded : ∀ {one two}, relation one two → (one ∈ first.current.packets ↔ two ∈ last.current.packets)
  facts : All₂ (FactPair relation) first.facts last.facts

namespace Related
variable {roles : Roles.RoleDecls} {relation : Packet roles → Packet roles → Prop} {first last : Tracked roles}

theorem models (same : Related relation first last) (facts : All₂ (FactPair relation) one two) (model) :
    GeneralNominalSettledSupport.Models first one model ↔ GeneralNominalSettledSupport.Models last two model := by
  unfold GeneralNominalSettledSupport.Models
  rw [same.source,same.coherent.facts_models facts model]

theorem slice (same : Related relation first last) (support model) : Slice first support model ↔ Slice last support model := by
  have forward : ∀ {a b : Tracked roles}, a.source = b.source →
      All₂ (FactPair relation) a.facts b.facts → Slice a support model → Slice b support model := by
    intro a b source facts valid
    refine ⟨source ▸ valid.1,?_⟩
    intro fact member included
    obtain ⟨other,found,pair⟩ := all₂_right facts member
    exact (same.coherent.holds pair model).mp
      (valid.2 other found (fun producer member => included producer (same.coherent.dependencies pair ▸ member)))
  constructor
  · exact forward same.source same.facts
  · intro valid
    refine ⟨same.source.symm ▸ valid.1,?_⟩
    intro fact member included
    obtain ⟨other,found,pair⟩ := all₂_left same.facts member
    exact (same.coherent.holds pair model).mpr
      (valid.2 other found (fun producer member => included producer ((same.coherent.dependencies pair).symm ▸ member)))

theorem packet_settled (same : Related relation first last) (pair : relation one two) :
    GeneralNominalSettledSupport.PacketSettled first.current one ↔ GeneralNominalSettledSupport.PacketSettled last.current two := by
  unfold GeneralNominalSettledSupport.PacketSettled GeneralNominalSettledSupport.Settled
  simp only [same.recorded pair,(same.coherent.sound pair).children,same.current.discharged]

theorem readback (same : Related relation first last) (facts : All₂ (FactPair relation) one two)
    (pair : relation packet other) : GeneralNominalSettledSupport.Readback first one packet ↔
      GeneralNominalSettledSupport.Readback last two other := by
  have condition : ∀ (state : Tracked roles) (facts : List (Fact roles)) (packet : Packet roles),
      GeneralNominalSettledSupport.Readback state facts packet ↔
        ∀ observation, Reads packet observation → ∀ model,
          GeneralNominalSettledSupport.Models state facts model → observation.Holds model := by
    intro state facts packet
    exact ⟨fun valid observation ⟨slot,member,test,head⟩ => valid slot member test observation head,
      fun valid slot member test observation head => valid observation ⟨slot,member,test,head⟩⟩
  rw [condition,condition]
  simp only [(same.coherent.sound pair).reads,same.models facts]

theorem merge_evidence (same : Related relation first last) (facts : All₂ (FactPair relation) one two) (a b : GeneralNominalDemandMerging.Site roles) :
    GeneralNominalSettledSupport.MergeEvidence (GeneralNominalSettledSupport.Models first one) a b ↔
      GeneralNominalSettledSupport.MergeEvidence (GeneralNominalSettledSupport.Models last two) a b := by
  have equal := funext (fun model => propext (same.models facts model))
  rw [equal]

theorem trusted {facts : List (Fact roles)} (same : Related relation first last) (trusted : GeneralNominalSettledSupport.Trusted first facts) :
    ∃ other, All₂ (FactPair relation) facts other ∧ GeneralNominalSettledSupport.Trusted last other := by
  induction trusted with
  | source => exact ⟨[],.nil,.source⟩
  | input packet support _ member readback ih =>
    obtain ⟨facts,pairs,trusted⟩ := ih
    obtain ⟨fact,present,pair⟩ := all₂_left same.facts member
    cases pair with
    | inputs pair =>
      exact ⟨_,.cons (.inputs pair) pairs,.input _ support trusted present ((same.readback pairs pair).mp readback)⟩
  | output packet support _ member included settled ih =>
    obtain ⟨facts,pairs,trusted⟩ := ih
    obtain ⟨fact,present,pair⟩ := all₂_left same.facts member
    cases pair with
    | outputs pair =>
      exact ⟨_,.cons (.outputs pair) pairs,.output _ support trusted present
        ((same.coherent.fact_members pairs (.inputs pair)).mp included) ((same.packet_settled pair).mp settled)⟩
  | merge a b support _ member evidence ih =>
    obtain ⟨facts,pairs,trusted⟩ := ih
    obtain ⟨fact,present,pair⟩ := all₂_left same.facts member
    cases pair with
    | merge => exact ⟨_,.cons .merge pairs,.merge a b support trusted present ((same.merge_evidence pairs a b).mp evidence)⟩

theorem symm (same : Related relation first last) : Related (fun last first => relation first last) last first := by
  refine ⟨same.coherent.symm,same.source.symm,same.current.symm,fun pair => (same.recorded pair).symm,?_⟩
  have flip : ∀ {a b}, All₂ (FactPair relation) a b → All₂ (FactPair (fun q p => relation p q)) b a := by
    intro a b pairs
    induction pairs with
    | nil => exact .nil
    | cons pair pairs ih =>
      refine .cons ?_ ih
      cases pair with
      | inputs pair => exact .inputs pair
      | outputs pair => exact .outputs pair
      | merge => exact .merge
  exact flip same.facts

theorem pool (same : Related relation first last) :
    GeneralNominalSupportChoices.dependencyPool first = GeneralNominalSupportChoices.dependencyPool last := by
  have equal : ∀ {a b}, All₂ (FactPair relation) a b → a.flatMap Fact.dependencies = b.flatMap Fact.dependencies := by
    intro a b pairs
    induction pairs with
    | nil => rfl
    | cons pair pairs ih => simp only [List.flatMap_cons,same.coherent.dependencies pair,ih]
  exact equal same.facts

theorem head_supported (same : Related relation first last) (support identity test) :
    HeadSupported first support identity test ↔ HeadSupported last support identity test := by
  simp only [HeadSupported,Entails,same.slice]

theorem available (same : Related relation first last) (identity test) :
    GeneralNominalDownstreamSupport.Available first identity test ↔ GeneralNominalDownstreamSupport.Available last identity test := by
  simp only [GeneralNominalDownstreamSupport.Available,same.pool,same.head_supported]

theorem ready (same : Related relation first last) (support identity) :
    ReadyAt first support identity ↔ ReadyAt last support identity := by
  have head : ∀ test observation, Head first.current.context.state identity test observation ↔
      Head last.current.context.state identity test observation := by
    obtain ⟨allocated,reserved,equal,_,_⟩ := same.current.context.state
    rw [equal]
    exact fun test observation => (GeneralNominalMetadataInspection.head _ _ _ _ test observation).symm
  simp only [ReadyAt,head,same.head_supported]

theorem settled_head (same : Related relation first last) (identity test) :
    GeneralNominalSettledSupport.HeadJustified first identity test ↔ GeneralNominalSettledSupport.HeadJustified last identity test := by
  have forward : ∀ {a b : Tracked roles} {r}, Related r a b →
      GeneralNominalSettledSupport.HeadJustified a identity test → GeneralNominalSettledSupport.HeadJustified b identity test := by
    intro a b r same justified
    obtain ⟨facts,trusted,snapshot,observation,head,valid⟩ := justified
    obtain ⟨other,pairs,trusted⟩ := same.trusted trusted
    exact ⟨other,trusted,snapshot,observation,head,fun model models => valid model ((same.models pairs model).mpr models)⟩
  exact ⟨forward same,forward same.symm⟩

end Related
end Yulang.GeneralNominalLedgerPermutation
