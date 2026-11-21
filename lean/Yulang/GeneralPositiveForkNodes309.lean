import Yulang.GeneralPositiveForkEvidence309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 15000000
namespace Yulang.GeneralPositiveForkNodes309
open GeneralPositiveForkSource309 (root compiled registry parent)
open GeneralPositiveForkPlan309 (loSite hiSite)
open GeneralPositiveForkInstall309 (after centers raw_sites inhabited reachable)
open GeneralPositiveForkEvidence309 (parentPlan parent_frame parent_children)
open GeneralPositiveForkLeaf309 (Side)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenters (Plan Site)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedJournal232 (Models)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedFrame231 (children)

inductive Node where | parent | low | high deriving DecidableEq
abbrev plan : Node → Plan roles
  | .parent => parentPlan
  | .low => GeneralPositiveForkLeaf309.plan .low
  | .high => GeneralPositiveForkLeaf309.plan .high

abbrev focus (n : Node) : Occurrence roles := (plan n).input.occurrence
abbrev key (n : Node) := (plan n).packet.declaration.id
abbrev site (n : Node) : Site roles := (plan n).input
abbrev links : Node → List Node | .parent => [.low,.high] | _ => []

theorem child_list (n : Node) : children (plan n).packet = (links n).map focus := by
  cases n
  · exact parent_children
  · exact GeneralPositiveForkLeaf309.no_children .low
  · exact GeneralPositiveForkLeaf309.no_children .high

theorem current_frame (n : Node) : Frame compiled after.core (focus n) (key n) (plan n) := by
  cases n
  · exact parent_frame
  · exact GeneralPositiveForkLeafFrame309.frame .low _ inhabited
  · exact GeneralPositiveForkLeafFrame309.frame .high _ inhabited

theorem raw_site (n : Node) : (plan n).packet.site = (site n).observed := by cases n <;> rfl
theorem role_key (n : Node) : (plan n).packet.declaration.role = (focus n).demand.role :=
  (current_frame n).role_eq
theorem role_injective : Function.Injective (fun n => (focus n).demand.role) := by
  intro a b e
  cases a <;> cases b <;> first | rfl | cases e

theorem center_known (c : Site roles) (member : c ∈ after.core.sites) :
    ∃ n, c = site n := by
  rw [centers] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · exact ⟨.parent,rfl⟩
  · exact ⟨.low,rfl⟩
  · exact ⟨.high,rfl⟩

theorem raw_known (s : GeneralNominalDemandMerging.Site roles)
    (mem : s ∈ after.core.erased.current.sites) : ∃ n, s = (site n).observed := by
  rw [raw_sites] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl
  · exact ⟨.parent,rfl⟩
  · exact ⟨.low,rfl⟩
  · exact ⟨.high,rfl⟩

theorem exact_frame (n : Node) {p : Plan roles} {k : Nat}
    (f : Frame compiled after.core (focus n) k p) : p = plan n := by
  have declaration : p.packet.declaration = (plan n).packet.declaration := by
    cases n
    · exact GeneralPositiveForkPreinstall309.member_parent f.visible f.role_eq
    · exact GeneralPositiveForkLeafFrame309.declaration_eq .low _ f.visible f.role_eq
    · exact GeneralPositiveForkLeafFrame309.declaration_eq .high _ f.visible f.role_eq
  have source : p.packet.site = (plan n).packet.site := by
    obtain ⟨j,h⟩ := raw_known _ f.raw_recorded
    rw [h,raw_site]
    have occ := h.symm ▸ f.occurrence_eq
    have role := congrArg (fun o : Occurrence roles => o.demand.role) occ
    cases role_injective role
    rfl
  have center : p.input = site n := by
    obtain ⟨j,h⟩ := center_known _ f.center_recorded
    have occ := h.symm ▸ (p.input_exact.trans f.occurrence_eq)
    have role := congrArg (fun o : Occurrence roles => o.demand.role) occ
    cases role_injective role
    exact h
  exact GeneralRebaseScopedFrame276.same_frame f (current_frame n) declaration source center

theorem generated_nodes (o : Occurrence roles)
    (h : GeneralNominalSaturationState.Generated after.core.erased.current root o) : ∃ n, o = focus n := by
  obtain ⟨s,member,exactOcc⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
    (GeneralNominalVersionedMixedTrace235.reachable reachable).1 h
  obtain ⟨n,siteEq⟩ := raw_known _ member
  exact ⟨n,exactOcc.symm.trans (congrArg GeneralNominalDemandMerging.Site.occurrence siteEq)⟩

end Yulang.GeneralPositiveForkNodes309
