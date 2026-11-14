import Yulang.GeneralNominalCenteredHeadMatPermutationPlans

set_option backward.isDefEq.respectTransparency false

/-! Site enumeration is immaterial: the centered emitter follows source clause
order, while its identities and the canonical child edges remain unchanged. -/
namespace Yulang.GeneralNominalCenteredHeadMatPermutationRaw
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalJournalPermutation (ContextPair PacketPair)
open GeneralNominalLedgerPermutation (All₂)
variable {roles : Roles.RoleDecls}

structure Raw (first last : GeneralNominalSaturationState.State roles) : Prop where
  context : ContextPair first.context last.context
  packets : All₂ PacketPair first.packets last.packets
  sites : ∀ site, site ∈ first.sites ↔ site ∈ last.sites
  edges : first.edges = last.edges
  aliases : first.aliases = last.aliases

namespace Raw
open GeneralNominalSaturationState
variable {first last : State roles}

theorem refl (state : State roles) : Raw state state := by
  refine ⟨ContextPair.refl _,?_,fun _ => Iff.rfl,rfl,rfl⟩
  induction state.packets with
  | nil => exact .nil
  | cons p ps ih => exact .cons (PacketPair.refl _) ih

theorem symm (same : Raw first last) : Raw last first := by
  refine ⟨same.context.symm,?_,fun site => (same.sites site).symm,same.edges.symm,same.aliases.symm⟩
  have swap : ∀ {xs ys : List (Packet roles)}, All₂ PacketPair xs ys → All₂ PacketPair ys xs := by
    intro xs ys pairs
    induction pairs with
    | nil => exact .nil
    | cons pair rest ih => exact .cons pair.symm ih
  exact swap same.packets

theorem packet_left (same : Raw first last) (member : packet ∈ first.packets) :
    ∃ other ∈ last.packets, PacketPair packet other := GeneralNominalLedgerPermutation.all₂_left same.packets member

theorem packet_right (same : Raw first last) (member : packet ∈ last.packets) :
    ∃ other ∈ first.packets, PacketPair other packet := GeneralNominalLedgerPermutation.all₂_right same.packets member

theorem alias (same : Raw first last) (one two : Nat) : Alias first one two ↔ Alias last one two := by
  have forward : ∀ {a b : State roles}, Raw a b → ∀ one two, Alias a one two → Alias b one two := by
    intro a b same one two path
    induction path with
    | refl => exact .refl _
    | edge member => exact .edge (same.aliases ▸ member)
    | symm _ ih => exact .symm ih
    | trans _ _ one two => exact .trans one two
  exact ⟨forward same one two,forward same.symm one two⟩

theorem generated (same : Raw first last) (root focus : Occurrence roles) :
    Generated first root focus ↔ Generated last root focus := by
  have forward : ∀ {a b : State roles}, Raw a b → ∀ {root focus}, Generated a root focus → Generated b root focus := by
    intro a b same root focus path
    induction path with
    | root => exact .root
    | child _ member ih => exact .child ih (same.edges ▸ member)
    | alias _ one two path ih => exact .alias ih ((same.sites _).mp one) ((same.sites _).mp two) ((same.alias _ _).mp path)
  exact ⟨forward same,forward same.symm⟩

theorem discharged (same : Raw first last) (focus : Occurrence roles) :
    GeneralNominalSupport.Discharged first focus ↔ GeneralNominalSupport.Discharged last focus := by
  have forward : ∀ {a b : State roles}, Raw a b → ∀ {focus},
      GeneralNominalSupport.Discharged a focus → GeneralNominalSupport.Discharged b focus := by
    intro a b same focus done
    induction done with
    | packet packet member children ih =>
      obtain ⟨other,found,pair⟩ := same.packet_left member
      rw [pair.site]
      exact .packet other found (fun child member => ih child (pair.children.symm ▸ member))
    | alias one two memberOne memberTwo path _ ih =>
      exact .alias one two ((same.sites _).mp memberOne) ((same.sites _).mp memberTwo) ((same.alias _ _).mp path) ih
  exact ⟨forward same,forward same.symm⟩

theorem waiting (same : Raw first last) (root focus : Occurrence roles) :
    GeneralNominalDownstreamSupport.Waiting first root focus ↔ GeneralNominalDownstreamSupport.Waiting last root focus := by
  have forward : ∀ {a b : State roles}, Raw a b → ∀ {root focus},
      GeneralNominalDownstreamSupport.Waiting a root focus → GeneralNominalDownstreamSupport.Waiting b root focus := by
    intro a b same root focus path
    induction path with
    | root unresolved => exact .root (fun done => unresolved ((same.discharged _).mpr done))
    | child _ member unresolved ih => exact .child ih (same.edges ▸ member) (fun done => unresolved ((same.discharged _).mpr done))
    | alias one two _ memberOne memberTwo path unresolved ih =>
      exact .alias one two ih ((same.sites _).mp memberOne) ((same.sites _).mp memberTwo) ((same.alias _ _).mp path)
        (fun done => unresolved ((same.discharged _).mpr done))
  exact ⟨forward same,forward same.symm⟩


theorem packet_settled (same : Raw first last) (pair : PacketPair one two)
    (recorded : one ∈ first.packets ↔ two ∈ last.packets) :
    GeneralNominalSettledSupport.PacketSettled first one ↔ GeneralNominalSettledSupport.PacketSettled last two := by
  simp only [GeneralNominalSettledSupport.PacketSettled,recorded,pair.children,same.discharged]

theorem regenerate (same : Raw first last) (contexts : ContextPair one two) :
    Raw (regenerate first one) (regenerate last two) :=
  ⟨contexts,same.packets,same.sites,same.edges,same.aliases⟩

theorem equate (same : Raw first last) (one two : Nat) :
    Raw (GeneralNominalFeedbackSteps.equate first one two) (GeneralNominalFeedbackSteps.equate last one two) :=
  ⟨⟨GeneralNominalMetadataEquivalence.extend same.context.state [] [] (fun _ => Iff.rfl) _,
    same.context.interpretation⟩,same.packets,same.sites,same.edges,same.aliases⟩

theorem enqueue (same : Raw first last) (focus : Occurrence roles) : Raw (enqueue first focus) (enqueue last focus) := by
  refine ⟨same.context,same.packets,?_,same.edges,same.aliases⟩
  intro site
  change site ∈ first.sites ++ _ ↔ site ∈ last.sites ++ _
  simp only [List.mem_append,same.sites]

theorem merge (same : Raw first last) (one two : GeneralNominalDemandMerging.Site roles) :
    Raw (merge first one two) (merge last one two) := by
  refine ⟨⟨GeneralNominalMetadataEquivalence.extend same.context.state [] [] (fun _ => Iff.rfl) _,
    same.context.interpretation⟩,same.packets,same.sites,same.edges,?_⟩
  exact congrArg (fun aliases => (one.occurrence.identity,two.occurrence.identity) :: aliases) same.aliases

end Raw

structure Snapshot (first last : GeneralNominalCenteredSteps.State roles) : Prop where
  raw : ∀ site, site ∈ first.erased.current.sites ↔ site ∈ last.erased.current.sites
  aliases : first.erased.current.aliases = last.erased.current.aliases
  centers : ∀ site, site ∈ first.sites ↔ site ∈ last.sites

namespace Snapshot
variable {first last : GeneralNominalCenteredSteps.State roles}

theorem refl (state : GeneralNominalCenteredSteps.State roles) : Snapshot state state :=
  ⟨fun _ => Iff.rfl,rfl,fun _ => Iff.rfl⟩

theorem symm (same : Snapshot first last) : Snapshot last first :=
  ⟨fun site => (same.raw site).symm,same.aliases.symm,fun site => (same.centers site).symm⟩

theorem alias (same : Snapshot first last) (one two) :
    GeneralNominalSaturationState.Alias first.erased.current one two ↔
      GeneralNominalSaturationState.Alias last.erased.current one two := by
  have forward {a b : GeneralNominalCenteredSteps.State roles} (equal : a.erased.current.aliases = b.erased.current.aliases)
      {one two} (path : GeneralNominalSaturationState.Alias a.erased.current one two) :
      GeneralNominalSaturationState.Alias b.erased.current one two := by
    induction path with
    | refl => exact .refl _
    | edge member => exact .edge (equal ▸ member)
    | symm _ ih => exact .symm ih
    | trans _ _ a b => exact .trans a b
  exact ⟨forward same.aliases,forward same.aliases.symm⟩

theorem requests (same : Snapshot first last) (root : Occurrence roles) (output) :
    output ∈ GeneralNominalCenteredHeadOutputs.requests first root ↔
      output ∈ GeneralNominalCenteredHeadOutputs.requests last root := by
  simp only [GeneralNominalCenteredHeadOutputs.mem_requests_iff,same.raw,same.alias]

theorem effects (same : Snapshot first last) (root : Occurrence roles) (plan : Plan roles) (model) :
    GeneralNominalCenteredHeadMatEffects.ClassEffects first root plan model ↔
      GeneralNominalCenteredHeadMatEffects.ClassEffects last root plan model := by
  simp only [GeneralNominalCenteredHeadMatEffects.ClassEffects,GeneralNominalCenteredHeadOutputs.EqualOutputs,same.requests]

theorem ready (same : Snapshot first last) (root : Occurrence roles) (plan : Plan roles) :
    GeneralNominalCenteredHeadMatEffects.Ready first root plan ↔
      GeneralNominalCenteredHeadMatEffects.Ready last root plan := by
  simp only [GeneralNominalCenteredHeadMatEffects.Ready,same.requests]

end Snapshot

structure Core (first last : GeneralNominalCenteredSteps.State roles) : Prop where
  current : Raw first.erased.current last.erased.current
  source : first.erased.source = last.erased.source
  centers : ∀ site, site ∈ first.sites ↔ site ∈ last.sites
  roots : first.sourceSites = last.sourceSites

namespace Core

theorem snapshot (same : Core first last) : Snapshot first last :=
  ⟨same.current.sites,same.current.aliases,same.centers⟩

theorem symm (same : Core first last) : Core last first :=
  ⟨same.current.symm,same.source.symm,fun site => (same.centers site).symm,same.roots.symm⟩

theorem refl (state : GeneralNominalCenteredSteps.State roles) : Core state state :=
  ⟨Raw.refl _,rfl,fun _ => Iff.rfl,rfl⟩

end Core
end Yulang.GeneralNominalCenteredHeadMatPermutationRaw
