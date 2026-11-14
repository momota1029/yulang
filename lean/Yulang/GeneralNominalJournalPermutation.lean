import Yulang.GeneralNominalMetadataEquivalence
import Yulang.GeneralNominalCenteredRegistryPassive

/-! The observation part of registry transport. Packet correspondence is shared
by the journal; metadata retains membership while allowing enumeration changes.
Certified observation views are transported independently of executable actions. -/
namespace Yulang.GeneralNominalJournalPermutation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
namespace Metadata
abbrev replace := GeneralNominalMetadataEquivalence.replace
abbrev Same := GeneralNominalMetadataEquivalence.Same
end Metadata

structure PacketPair (first last : Packet roles) : Prop where
  site : first.site = last.site
  children : first.children = last.children
  identity : first.declaration.id = last.declaration.id
  holds : ∀ model, first.Holds model ↔ last.Holds model
  inputs : ∀ model, GeneralNominalPacketSupport.Inputs first model ↔ GeneralNominalPacketSupport.Inputs last model
  outputs : ∀ model, GeneralNominalPacketSupport.Outputs first model ↔ GeneralNominalPacketSupport.Outputs last model

namespace PacketPair

theorem refl (packet : Packet roles) : PacketPair packet packet :=
  ⟨rfl,rfl,rfl,fun _ => Iff.rfl,fun _ => Iff.rfl,fun _ => Iff.rfl⟩

theorem symm (pair : PacketPair first last) : PacketPair last first :=
  ⟨pair.site.symm,pair.children.symm,pair.identity.symm,
    fun model => (pair.holds model).symm,fun model => (pair.inputs model).symm,fun model => (pair.outputs model).symm⟩

theorem rebase (packet : Packet roles) (order : GeneralRegistryReordering.Reorders packet.registry registry)
    (pair : GeneralRegistryReordering.DeclarationReorders packet.declaration declaration)
    (roleEq : packet.registry.roles = roles) :
    PacketPair packet (GeneralNominalPacketReordering.rebase packet order pair) := by
  exact ⟨rfl,(GeneralNominalPacketReordering.children order pair).symm,pair.1,
    fun model => (GeneralNominalPacketReordering.holds order pair roleEq model).symm,
    fun model => (GeneralNominalPacketReordering.inputs order pair model).symm,
    fun model => (GeneralNominalPacketReordering.outputs order pair roleEq model).symm⟩
end PacketPair

structure ContextPair (first last : GeneralNominalCandidates.Context) : Prop where
  state : Metadata.Same first.state last.state
  interpretation : first.interpretation = last.interpretation

namespace ContextPair

theorem refl (context : GeneralNominalCandidates.Context) : ContextPair context context :=
  ⟨GeneralNominalMetadataEquivalence.refl _,rfl⟩

theorem symm (same : ContextPair first last) : ContextPair last first :=
  ⟨GeneralNominalMetadataEquivalence.symm same.state,same.interpretation.symm⟩

theorem replace_form (same : ContextPair first last) :
    ∃ allocated reserved, last = ⟨Metadata.replace first.state allocated reserved,first.interpretation⟩ ∧
      (∀ key, key ∈ allocated ↔ key ∈ first.state.allocated) ∧
      ∀ name, name ∈ reserved ↔ name ∈ first.state.reserved := by
  obtain ⟨allocated,reserved,equal,keys,names⟩ := same.state
  refine ⟨allocated,reserved,?_,keys,names⟩
  have interpretation := same.interpretation
  cases first; cases last
  simp_all
end ContextPair

structure Related (first last : State roles) : Prop where
  context : ContextPair first.context last.context
  packets : CommonRoleOutermostResolver.All₂ PacketPair first.packets last.packets
  sites : first.sites = last.sites
  edges : first.edges = last.edges
  aliases : first.aliases = last.aliases

private theorem paired_mem_left {α β : Type} {relation : α → β → Prop}
    {first : List α} {last : List β} {value : α}
    (pairs : CommonRoleOutermostResolver.All₂ relation first last) (member : value ∈ first) :
    ∃ other ∈ last, relation value other := by
  induction pairs with
  | nil => cases member
  | @cons a b as bs pair rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨b,List.mem_cons_self ..,pair⟩
    · obtain ⟨other,found,same⟩ := ih member
      exact ⟨other,List.mem_cons_of_mem _ found,same⟩

namespace Related
variable {roles : Roles.RoleDecls} {first last : State roles}

theorem refl (state : State roles) : Related state state := by
  refine ⟨ContextPair.refl _,?_,rfl,rfl,rfl⟩
  induction state.packets with
  | nil => exact .nil
  | cons packet packets ih => exact .cons (PacketPair.refl _) ih

theorem symm (same : Related first last) : Related last first := by
  refine ⟨same.context.symm,?_,same.sites.symm,same.edges.symm,same.aliases.symm⟩
  have swap : ∀ {xs ys : List (Packet roles)}, CommonRoleOutermostResolver.All₂ PacketPair xs ys →
      CommonRoleOutermostResolver.All₂ PacketPair ys xs := by
    intro xs ys pairs
    induction pairs with
    | nil => exact .nil
    | cons pair rest ih => exact .cons pair.symm ih
  exact swap same.packets

theorem packet_left (same : Related first last) (member : packet ∈ first.packets) :
    ∃ other ∈ last.packets, PacketPair packet other := paired_mem_left same.packets member

theorem packet_right (same : Related first last) (member : packet ∈ last.packets) :
    ∃ other ∈ first.packets, PacketPair other packet := by
  obtain ⟨other,found,pair⟩ := same.symm.packet_left member
  exact ⟨other,found,pair.symm⟩

theorem journal (same : Related first last) (model : Assignment) :
    (∀ packet ∈ first.packets, packet.Holds model) ↔ ∀ packet ∈ last.packets, packet.Holds model := by
  constructor
  · intro valid packet member
    obtain ⟨other,found,pair⟩ := same.packet_right member
    exact (pair.holds model).mp (valid other found)
  · intro valid packet member
    obtain ⟨other,found,pair⟩ := same.packet_left member
    exact (pair.holds model).mpr (valid other found)

theorem models (same : Related first last) (model : Assignment) : Models first model ↔ Models last model := by
  unfold Models
  rw [GeneralNominalMetadataEquivalence.models same.context.state,same.journal model,same.sites]

theorem alias (same : Related first last) (one two : Nat) : Alias first one two ↔ Alias last one two := by
  have forward : ∀ {a b : State roles}, Related a b → ∀ one two, Alias a one two → Alias b one two := by
    intro a b same one two path
    induction path with
    | refl => exact .refl _
    | edge member => exact .edge (same.aliases ▸ member)
    | symm _ ih => exact .symm ih
    | trans _ _ one two => exact .trans one two
  exact ⟨forward same one two,forward same.symm one two⟩

theorem generated (same : Related first last) (root focus : Occurrence roles) :
    Generated first root focus ↔ Generated last root focus := by
  have forward : ∀ {a b : State roles}, Related a b → ∀ {root focus}, Generated a root focus → Generated b root focus := by
    intro a b same root focus path
    induction path with
    | root => exact .root
    | child _ member ih => exact .child ih (same.edges ▸ member)
    | alias _ one two path ih => exact .alias ih (same.sites ▸ one) (same.sites ▸ two) ((same.alias _ _).mp path)
  exact ⟨forward same,forward same.symm⟩

theorem discharged (same : Related first last) (focus : Occurrence roles) :
    GeneralNominalSupport.Discharged first focus ↔ GeneralNominalSupport.Discharged last focus := by
  have forward : ∀ {a b : State roles}, Related a b → ∀ {focus},
      GeneralNominalSupport.Discharged a focus → GeneralNominalSupport.Discharged b focus := by
    intro a b same focus done
    induction done with
    | packet packet member children ih =>
      obtain ⟨other,found,pair⟩ := same.packet_left member
      rw [pair.site]
      exact .packet other found (fun child member => ih child (pair.children.symm ▸ member))
    | alias one two memberOne memberTwo path _ ih =>
      exact .alias one two (same.sites ▸ memberOne) (same.sites ▸ memberTwo) ((same.alias _ _).mp path) ih
  exact ⟨forward same,forward same.symm⟩

theorem waiting (same : Related first last) (root focus : Occurrence roles) :
    GeneralNominalDownstreamSupport.Waiting first root focus ↔ GeneralNominalDownstreamSupport.Waiting last root focus := by
  have forward : ∀ {a b : State roles}, Related a b → ∀ {root focus},
      GeneralNominalDownstreamSupport.Waiting a root focus → GeneralNominalDownstreamSupport.Waiting b root focus := by
    intro a b same root focus path
    induction path with
    | root unresolved => exact .root (fun done => unresolved ((same.discharged _).mpr done))
    | child _ member unresolved ih => exact .child ih (same.edges ▸ member) (fun done => unresolved ((same.discharged _).mpr done))
    | alias one two _ memberOne memberTwo path unresolved ih =>
      exact .alias one two ih (same.sites ▸ memberOne) (same.sites ▸ memberTwo) ((same.alias _ _).mp path)
        (fun done => unresolved ((same.discharged _).mpr done))
  exact ⟨forward same,forward same.symm⟩

theorem regenerate (same : Related first last) (contexts : ContextPair one two) :
    Related (GeneralNominalSaturationState.regenerate first one) (GeneralNominalSaturationState.regenerate last two) :=
  ⟨contexts,same.packets,same.sites,same.edges,same.aliases⟩

noncomputable def refresh {context : GeneralNominalCandidates.Context} (same : Related first last) (certificate : GeneralNominalCycleSteps.Refresh first context) :
    GeneralNominalCycleSteps.Refresh last context where
  refines := GeneralNominalMetadataEquivalence.refines_left same.context.state certificate.refines
  interpretation := certificate.interpretation.trans same.context.interpretation
  exact := fun model valid => certificate.exact model ((same.models model).mpr valid)
  support := fun source member => (GeneralNominalMetadataEquivalence.sources same.context.state source).mp (certificate.support source member)


theorem reobserve (same : Related first last) (revision : GeneralNominalReobservationSteps.Revision first) :
    ∃ other : GeneralNominalReobservationSteps.Revision last,
      Related revision.result other.result ∧
      (GeneralNominalReobservationSteps.Certified revision → GeneralNominalReobservationSteps.Certified other) ∧
      (GeneralNominalReobservationSteps.Improves revision ↔ GeneralNominalReobservationSteps.Improves other) := by
  rcases first with ⟨one,packets,sites,edges,aliases⟩
  rcases last with ⟨two,otherPackets,otherSites,otherEdges,otherAliases⟩
  obtain ⟨allocated,reserved,contextEq,keys,names⟩ := same.context.replace_form
  dsimp at contextEq
  subst two
  let other : GeneralNominalReobservationSteps.Revision
      ⟨⟨Metadata.replace one.state allocated reserved,one.interpretation⟩,otherPackets,otherSites,otherEdges,otherAliases⟩ :=
    ⟨revision.entries,revision.catalogue,revision.opaqueHeads,revision.domain⟩
  have snapshots : Metadata.Same revision.snapshot other.snapshot := ⟨allocated,reserved,rfl,keys,names⟩
  have result : Related revision.result other.result :=
    ⟨⟨snapshots,rfl⟩,same.packets,same.sites,same.edges,same.aliases⟩
  refine ⟨other,result,?_,Iff.rfl⟩
  intro certificate
  exact ⟨fun model valid => (GeneralNominalMetadataEquivalence.models same.context.state model).mp
    (certificate.raw model ((GeneralNominalMetadataEquivalence.models snapshots model).mpr valid)),
    fun model => (result.models model).symm.trans ((certificate.exact model).trans (same.models model))⟩

theorem view (same : Related first last) (path : GeneralNominalDownstreamSupport.View first observed) :
    ∃ other, GeneralNominalDownstreamSupport.View last other ∧ Related observed other := by
  induction path with
  | current => exact ⟨last,.current,same⟩
  | refresh _ certificate ih =>
    obtain ⟨other,path,related⟩ := ih
    exact ⟨_,.refresh path (related.refresh certificate),related.regenerate (ContextPair.refl _)⟩
  | reobserve revision _ certificate ih =>
    obtain ⟨other,path,related⟩ := ih
    obtain ⟨next,pair,certified,_⟩ := related.reobserve revision
    exact ⟨next.result,.reobserve next path (certified certificate),pair⟩

theorem equate (same : Related first last) (one two : Nat) :
    Related (GeneralNominalFeedbackSteps.equate first one two) (GeneralNominalFeedbackSteps.equate last one two) :=
  ⟨⟨GeneralNominalMetadataEquivalence.extend same.context.state [] [] (fun _ => Iff.rfl) _,
    same.context.interpretation⟩,same.packets,same.sites,same.edges,same.aliases⟩

theorem enqueue (same : Related first last) (focus : Occurrence roles) :
    Related (GeneralNominalSaturationState.enqueue first focus) (GeneralNominalSaturationState.enqueue last focus) :=
  ⟨same.context,same.packets,congrArg (· ++ [GeneralNominalDemandMerging.pointSite focus]) same.sites,same.edges,same.aliases⟩

theorem equal (same : Related first last) (one two : Nat) :
    GeneralNominalFeedbackK2.Equal first one two ↔ GeneralNominalFeedbackK2.Equal last one two := by
  unfold GeneralNominalFeedbackK2.Equal GeneralNominalFeedbackSites.EndpointEqual
  simp only [same.models]

theorem rawEqual (same : Related first last) (one two : Nat) :
    GeneralNominalFeedbackSteps.RawEqual first one two ↔ GeneralNominalFeedbackSteps.RawEqual last one two := by
  unfold GeneralNominalFeedbackSteps.RawEqual
  simp only [GeneralNominalMetadataEquivalence.models same.context.state]

theorem administrative {focus : Occurrence roles} (same : Related first last)
    (action : GeneralNominalSharedSteps.Administrative registry first focus next) (otherRegistry : Registry) :
    ∃ other, GeneralNominalSharedSteps.Administrative otherRegistry last focus other ∧ Related next other := by
  cases action with
  | enqueue linked absent =>
    exact ⟨_,.enqueue focus ((GeneralNominalMetadataEquivalence.linked same.context.state _).mp linked)
      (fun site member => absent site (same.sites.symm ▸ member)),same.enqueue focus⟩
  | refresh context certificate source member unknown known =>
    exact ⟨_,.refresh focus context (same.refresh certificate) source
      ((GeneralNominalMetadataEquivalence.sources same.context.state _).mp member)
      (fun known => unknown ((GeneralNominalMetadataEquivalence.known same.context.state _).mpr known)) known,
      same.regenerate (ContextPair.refl _)⟩
  | equate one two firstPresent lastPresent equal novel =>
    exact ⟨_,.equate focus one two
      ((GeneralNominalMetadataEquivalence.sources same.context.state _).mp firstPresent)
      ((GeneralNominalMetadataEquivalence.sources same.context.state _).mp lastPresent)
      ((same.equal one two).mp equal) (fun equal => novel ((same.rawEqual one two).mpr equal)),same.equate one two⟩
  | reobserve revision certificate improved =>
    obtain ⟨other,pair,certified,improves⟩ := same.reobserve revision
    exact ⟨_,.reobserve focus other (certified certificate) (improves.mp improved),pair⟩

end Related
end Yulang.GeneralNominalJournalPermutation
