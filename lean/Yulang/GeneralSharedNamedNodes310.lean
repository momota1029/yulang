import Yulang.GeneralSharedNamedCurrent310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 15000000
namespace Yulang.GeneralSharedNamedNodes310
open GeneralSharedNamedSource310 (root compiled registry impl)
open GeneralSharedNamedPlan310 (loSite hiSite)
open GeneralSharedNamedInstall310 (centers raw_sites)
open GeneralSharedNamedMerge310 (merged reached inhabited)
open GeneralSharedNamedCurrent310 (parent receiver current_parent current_leaf centers_same raw_same)
open GeneralSharedNamedEvidence310 (parentPlan parent_children)
open GeneralSharedNamedLeaf310 (Side)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenters (Plan Site)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedJournal232 (Models)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedFrame231 (children)

inductive Node where | parent | low | high deriving DecidableEq
abbrev plan : Node → Plan roles
  | .parent => parent
  | .low => receiver .low
  | .high => receiver .high

abbrev focus (n : Node) : Occurrence roles := (plan n).input.occurrence
abbrev key (n : Node) := (plan n).packet.declaration.id
abbrev site (n : Node) : Site roles := (plan n).input
abbrev links : Node → List Node | .parent => [.low,.high] | _ => []

theorem child_list (n : Node) : children (plan n).packet = (links n).map focus := by
  cases n
  · change children (GeneralNominalVersionedTransport231.extendedPacket [] GeneralSharedNamedMerge310.added [] parentPlan.packet) = _
    rw [GeneralNominalVersionedTransport231.children_eq,parent_children]
    rfl
  · change children (GeneralNominalVersionedTransport231.extendedPacket [] GeneralSharedNamedMerge310.added []
      (GeneralSharedNamedLeaf310.packet .low)) = _
    rw [GeneralNominalVersionedTransport231.children_eq,GeneralSharedNamedLeaf310.no_children]
    rfl
  · change children (GeneralNominalVersionedTransport231.extendedPacket [] GeneralSharedNamedMerge310.added []
      (GeneralSharedNamedLeaf310.packet .high)) = _
    rw [GeneralNominalVersionedTransport231.children_eq,GeneralSharedNamedLeaf310.no_children]
    rfl

theorem current_frame (n : Node) : Frame compiled merged.core (focus n) (key n) (plan n) := by
  cases n
  · exact current_parent
  · exact current_leaf .low
  · exact current_leaf .high

theorem raw_site (n : Node) : (plan n).packet.site = (site n).observed := by cases n <;> rfl
theorem role_key (n : Node) : (plan n).packet.declaration.role = (focus n).demand.role :=
  (current_frame n).role_eq
theorem center_known (c : Site roles) (member : c ∈ merged.core.sites) :
    ∃ n, c = site n := by
  rw [centers_same,centers] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · exact ⟨.parent,rfl⟩
  · exact ⟨.low,rfl⟩
  · exact ⟨.high,rfl⟩

theorem raw_known (s : GeneralNominalDemandMerging.Site roles)
    (mem : s ∈ merged.core.erased.current.sites) : ∃ n, s = (site n).observed := by
  rw [raw_same,raw_sites] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl
  · exact ⟨.parent,rfl⟩
  · exact ⟨.low,rfl⟩
  · exact ⟨.high,rfl⟩

theorem focus_injective : Function.Injective focus := by
  intro a b same
  have ident := congrArg Occurrence.identity same
  cases a <;> cases b <;> first | rfl |
    exact False.elim (GeneralSharedNamedLeafFrame310.invocations .low ident) |
    exact False.elim (GeneralSharedNamedLeafFrame310.invocations .high ident) |
    exact False.elim (GeneralSharedNamedLeafFrame310.invocations .low ident.symm) |
    exact False.elim (GeneralSharedNamedLeafFrame310.invocations .high ident.symm) |
    exact False.elim (GeneralSharedNamedEvidence310.siblings_different ident) |
    exact False.elim (GeneralSharedNamedEvidence310.siblings_different ident.symm)

theorem generated_nodes (o : Occurrence roles)
    (h : GeneralNominalSaturationState.Generated merged.core.erased.current root o) : ∃ n, o = focus n := by
  obtain ⟨s,member,exactOcc⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
    (GeneralNominalVersionedMixedTrace235.reachable reached).1 h
  obtain ⟨n,siteEq⟩ := raw_known _ member
  exact ⟨n,exactOcc.symm.trans (congrArg GeneralNominalDemandMerging.Site.occurrence siteEq)⟩

end Yulang.GeneralSharedNamedNodes310
