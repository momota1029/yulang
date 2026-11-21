import Yulang.GeneralWhereVersionRootSafety317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralWhereVersionRootRegistry317
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry declaration leaf)
open GeneralWhereVersionCase317 (occ site)
open GeneralWhereVersionCommit317 (core framedState requests_iff)
open GeneralWhereVersionLeafRegistry317 (descriptors sites corrected_not_root rRaw rSite)
open GeneralWhereVersionRootReport317 (packet plan location)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralLiveCompoundPost316 (raw_sites_after)
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem found_raw {x} (present : x ∈ core.erased.current.sites) (focus : x.occurrence = root) :
    x = rRaw := by
  rw [descriptors] at present
  rcases List.mem_cons.mp present with eq|other
  · exact eq
  · rcases List.mem_cons.mp other with rfl|last
    · exact False.elim (GeneralLiveCompoundCurrentRoot316.not_root focus)
    · cases List.mem_singleton.mp last
      exact False.elim (corrected_not_root focus)

theorem found_center {x : Site roles} (present : x ∈ core.sites) (focus : x.occurrence = root) :
    x = rSite := by
  rw [sites] at present
  rcases List.mem_cons.mp present with eq|other
  · exact eq
  · rcases List.mem_cons.mp other with rfl|last
    · exact False.elim (GeneralLiveCompoundCurrentRoot316.not_root focus)
    · cases List.mem_singleton.mp last
      exact False.elim (corrected_not_root focus)

theorem administrative : AdministrativeReady framedState root := by
  refine ⟨⟨rSite,sites ▸ List.mem_cons_self,rfl⟩,?_⟩
  intro first present owned last locate same
  cases found_center present owned
  change last ∈ core.sites at locate
  rw [sites] at locate
  rcases List.mem_cons.mp locate with rfl|other
  · exact .refl _
  · rcases List.mem_cons.mp other with rfl|one
    · have impossible : (0:Nat) = 1 := same.1
      cases impossible
    · cases List.mem_singleton.mp one
      have impossible : (0:Nat) = 1 := same.1
      cases impossible

theorem unique_frame {p : Plan roles} {key : Nat} (h : Frame registry core root key p) : p = plan := by
  apply GeneralLiveCompoundPostFrames316.frame_unique (focus := root) (last := plan) h.registry_eq h.context_eq
  · rcases List.mem_cons.mp h.visible with a|last
    · exact a
    · have eq := List.mem_singleton.mp last
      have role := h.role_eq
      rw [eq] at role
      have clash : (1:Nat) = 0 := role
      cases clash
  · exact found_raw h.raw_recorded h.occurrence_eq
  · exact found_center h.center_recorded (p.input_exact.trans h.occurrence_eq)
  · exact h.located
  · exact location

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready core root plan := by
  intro out member
  have old := (requests_iff root out).mp member
  cases GeneralLiveCompoundAdmin316.all_requests raw_sites_after old
  exact ⟨.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩,rfl,rfl⟩

theorem classes (m : Assignment) (valid : ParentHolds m) :
    GeneralNominalVersionedEffects231.ClassEffects core root plan m := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  refine ⟨?_,GeneralWhereVersionLeafRegistry317.equal_outputs m root⟩
  intro out member body found
  cases GeneralLiveCompoundAdmin316.all_requests raw_sites_after ((requests_iff root out).mp member)
  have exactBody : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
  subst body
  intro row seen
  cases List.mem_singleton.mp seen
  change Equivalent (m 4).1 GeneralDictionaryOptionalOutput229.value
  exact GeneralWhereVersionWitness317.actual_row m valid.1

end Yulang.GeneralWhereVersionRootRegistry317
