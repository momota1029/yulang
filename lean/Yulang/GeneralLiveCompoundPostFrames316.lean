import Yulang.GeneralLiveCompoundPostFeedback316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 37000000
namespace Yulang.GeneralLiveCompoundPostFrames316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry declaration leaf)
open GeneralLiveCompoundChildSite316
open GeneralLiveCompoundLeafInstall316 (after models)
open GeneralLiveCompoundPost316 (raw cur raw_sites_after centers_after aliases_after)
open GeneralNominalVersionedInstallation231 (reserved atoms allocated replayPlan)
open GeneralNominalVersionedTransport231 (extendedPlan)
open GeneralLiveCompoundLeafHead316 (packet)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedCandidates231 (inputs)

noncomputable abbrev rootPlan : Plan roles :=
  extendedPlan (reserved packet) (atoms packet) (allocated packet) GeneralLiveCompoundCurrentRoot316.plan
noncomputable abbrev leafPlan : Plan roles := replayPlan GeneralLiveCompoundLeafHead316.plan

theorem frame_unique {focus : Occurrence roles} {first last : Plan roles}
    (regOne : first.packet.registry = last.packet.registry)
    (ctxOne : first.packet.context = last.packet.context)
    (decl : first.packet.declaration = last.packet.declaration)
    (rawEq : first.packet.site = last.packet.site)
    (sites : first.input = last.input)
    (locFirst : GeneralNominalRecursiveCandidates.arguments first.packet.context (inputs focus) = some first.packet.bounds)
    (locLast : GeneralNominalRecursiveCandidates.arguments last.packet.context (inputs focus) = some last.packet.bounds) :
    first = last := by
  rcases first with ⟨⟨a,b,c,d,e,f⟩,g,h⟩
  rcases last with ⟨⟨i,j,k,l,m,n⟩,o,p⟩
  have A : a = i := regOne
  have B : b = j := ctxOne
  have C : c = k := rawEq
  have D : d = l := decl
  have G : g = o := sites
  subst a; subst b; subst c; subst d; subst g
  have eq : f = n := Option.some.inj (locFirst.symm.trans locLast)
  subst f
  rfl

theorem root_frame_plan {key} {p : Plan roles}
    (h : Frame registry after.core root key p) : p = rootPlan := by
  apply frame_unique (focus := root) (last := rootPlan) h.registry_eq h.context_eq
  · rcases List.mem_cons.mp h.visible with one | two
    · exact one
    · have eq := List.mem_singleton.mp two
      have role := h.role_eq
      rw [eq] at role
      cases role
  · have seen := h.raw_recorded
    rw [raw_sites_after] at seen
    rcases List.mem_cons.mp seen with same | last
    · exact same
    · have eq := congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp last)
      exact False.elim (GeneralLiveCompoundCurrentRoot316.not_root (eq.symm.trans h.occurrence_eq))
  · have seen := h.center_recorded
    rw [centers_after] at seen
    rcases List.mem_cons.mp seen with same | last
    · exact same
    · have eq := congrArg Site.occurrence (List.mem_singleton.mp last)
      exact False.elim (GeneralLiveCompoundCurrentRoot316.not_root (eq.symm.trans (p.input_exact.trans h.occurrence_eq)))
  · exact h.located
  · exact GeneralLiveCompoundCurrentRoot316.located

theorem leaf_frame_plan {key} {p : Plan roles}
    (h : Frame registry after.core child key p) : p = leafPlan := by
  apply frame_unique (focus := child) (last := leafPlan) h.registry_eq h.context_eq
  · rcases List.mem_cons.mp h.visible with one | two
    · have role := h.role_eq
      rw [one] at role; cases role
    · exact List.mem_singleton.mp two
  · have seen := h.raw_recorded
    rw [raw_sites_after] at seen
    rcases List.mem_cons.mp seen with same | last
    · exact False.elim (GeneralLiveCompoundCurrentRoot316.not_root ((congrArg GeneralNominalDemandMerging.Site.occurrence same).symm.trans h.occurrence_eq).symm)
    · exact List.mem_singleton.mp last
  · have seen := h.center_recorded
    rw [centers_after] at seen
    rcases List.mem_cons.mp seen with same | last
    · have occ := p.input_exact.trans h.occurrence_eq
      rw [same] at occ
      exact False.elim (GeneralLiveCompoundCurrentRoot316.not_root occ.symm)
    · exact List.mem_singleton.mp last
  · exact h.located
  · exact located

theorem leaf_held {m} (valid : GeneralNominalVersionedJournal232.Models after m) :
    GeneralNominalVersionedPlans231.Holds leafPlan m :=
  (GeneralNominalVersionedInstallation231.replay_holds_iff ..).mpr ((models m).mp valid).2

theorem leaf_committed : GeneralNominalVersionedMixedKernel234.Committed after leafPlan := by
  refine ⟨fun m valid => ⟨leaf_held valid,GeneralLiveCompoundAdmin316.leaf_classes raw_sites_after aliases_after leafPlan⟩,?_⟩
  have absent : GeneralNominalVersionedFrame231.children leafPlan.packet = [] := by
    unfold leafPlan replayPlan
    rw [GeneralNominalVersionedTransport231.plan_packet,
      GeneralNominalVersionedTransport231.children_eq,GeneralLiveCompoundLeafEvidence316.terminal]
  intro child member
  rw [absent] at member
  cases member

theorem leaf_frame : Frame registry after.core child leaf.id leafPlan := by
  have first := GeneralLiveCompoundLeafEvidence316.frame
  have carried := GeneralDepthTwoFrameCarry300.frame_carried (reserved packet) (atoms packet) (allocated packet)
    registry _ child leaf.id _ first
    (fun n h => List.mem_append_right _ h) _ GeneralLiveCompoundPost316.leaf_replayed
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,first.visible,first.role_eq,carried.located,carried.prepared⟩
  · rw [raw_sites_after]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · rw [centers_after]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem leaf_evidence {m} (valid : GeneralNominalVersionedJournal232.Models after m) :
    GeneralNominalVersionedEvidence231.Evidence registry after.core m child (.node leaf.id []) := by
  apply GeneralNominalVersionedEvidence231.evidence_leaf
  refine ⟨leafPlan,leaf_frame,?_,leaf_held valid,?_⟩
  · unfold leafPlan replayPlan
    rw [GeneralNominalVersionedTransport231.plan_packet,GeneralNominalVersionedTransport231.children_eq,
      GeneralLiveCompoundLeafEvidence316.terminal]
  · intro out absent; cases absent

theorem no_root_packet {m} (valid : GeneralNominalVersionedJournal232.Models after m) :
    ¬ GeneralNominalVersionedPlans231.Holds rootPlan m := by
  intro packetModel
  exact GeneralLiveCompoundStaleRoot316.no_current_packet m ((models m).mp valid).1
    ((GeneralNominalVersionedTransport231.holds_iff ..).mp packetModel).1

theorem no_root_evidence {m} (valid : GeneralNominalVersionedJournal232.Models after m) (payload) :
    ¬ GeneralNominalVersionedEvidence231.Evidence registry after.core m root payload := by
  intro found
  have indexed := (GeneralDictionaryReadback.payload_iff_erased ..).mpr found
  cases indexed with
  | node inst tail =>
    obtain ⟨p,h⟩ := inst
    exact no_root_packet valid (by simpa only [root_frame_plan h.frame] using h.packet)

end Yulang.GeneralLiveCompoundPostFrames316
