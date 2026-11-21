import Yulang.GeneralWhereVersionLeafSafety317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31000
set_option maxHeartbeats 41000000
namespace Yulang.GeneralWhereVersionLeafRegistry317
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry leaf declaration)
open GeneralLiveCompoundChildSite316 (child childSite)
open GeneralLiveCompoundPost316 (raw raw_sites_after centers_after)
open GeneralWhereVersionCase317 (occ site lower descriptor)
open GeneralWhereVersionBase317 (lower_fresh)
open GeneralWhereVersionCommit317 (core framedState raw_aliases requests_iff)
open GeneralWhereVersionLeafHead317 (packet plan located)
open GeneralWhereVersionLeafFresh317 (owner_eq)
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev rSite := rootSite snapshot.seed root
abbrev rRaw := GeneralNominalDemandMerging.pointSite root

theorem corrected_not_root : occ ≠ root := by
  intro eq
  have bad : (1:Nat) = 0 := congrArg (fun d : Occurrence roles => d.demand.role) eq
  cases bad

theorem corrected_not_old : occ ≠ child := by
  intro eq
  have same := congrArg (fun d : Occurrence roles => (d.demand.arguments (0 : Fin 1)).1) eq
  rw [show (occ.demand.arguments (0 : Fin 1)).1 = lower from congrArg Prod.fst descriptor] at same
  have present : (child.demand.arguments (0 : Fin 1)).1 ∈ GeneralNominalState.sources raw :=
    GeneralNominalAllocationSupport.slot_source raw (5 : Fin 8)
  exact lower_fresh (same.symm ▸ present)

theorem descriptors : core.erased.current.sites = [rRaw,childSite.observed,site.observed] := by
  change GeneralLiveCompoundLeafInstall316.after.core.erased.current.sites ++ [site.observed] = _
  rw [raw_sites_after]; rfl

theorem sites : core.sites = [rSite,childSite,site] := by
  change GeneralLiveCompoundLeafInstall316.after.core.sites ++ [site] = _
  rw [centers_after]; rfl

theorem found_raw {x} (seen : x ∈ core.erased.current.sites) (focus : x.occurrence = occ) :
    x = site.observed := by
  rw [descriptors] at seen
  rcases List.mem_cons.mp seen with rfl|rest
  · exact False.elim (corrected_not_root focus.symm)
  · rcases List.mem_cons.mp rest with rfl|last
    · exact False.elim (corrected_not_old focus.symm)
    · exact List.mem_singleton.mp last

theorem found_center {x : Site roles} (seen : x ∈ core.sites) (focus : x.occurrence = occ) :
    x = site := by
  rw [sites] at seen
  rcases List.mem_cons.mp seen with rfl|rest
  · exact False.elim (corrected_not_root focus.symm)
  · rcases List.mem_cons.mp rest with rfl|last
    · exact False.elim (corrected_not_old focus.symm)
    · exact List.mem_singleton.mp last

theorem same_role_owner (x : Site roles) (seen : x ∈ core.sites) (role : x.occurrence.demand.role = occ.demand.role) :
    x.occurrence.identity = occ.identity := by
  rw [sites] at seen
  rcases List.mem_cons.mp seen with rfl|rest
  · have h : (0:Nat) = 1 := role
    cases h
  · rcases List.mem_cons.mp rest with rfl|last
    · exact owner_eq.symm
    · cases List.mem_singleton.mp last; rfl

theorem administrative : AdministrativeReady framedState occ := by
  refine ⟨⟨site,List.mem_append_right _ (List.mem_singleton_self _),rfl⟩,?_⟩
  intro a seen focus b inside same
  cases found_center seen focus
  have owner := same_role_owner b inside same.1.symm
  exact owner.symm ▸ GeneralNominalSaturationState.Alias.refl _

theorem unique_frame {p : Plan roles} {key : Nat} (h : Frame registry core occ key p) : p = plan := by
  apply GeneralLiveCompoundPostFrames316.frame_unique (focus := occ) (last := plan) h.registry_eq h.context_eq
  · rcases List.mem_cons.mp h.visible with one | last
    · have role := h.role_eq
      rw [one] at role
      have bad : (0:Nat) = 1 := role
      cases bad
    · exact List.mem_singleton.mp last
  · exact found_raw h.raw_recorded h.occurrence_eq
  · exact found_center h.center_recorded (p.input_exact.trans h.occurrence_eq)
  · exact h.located
  · exact located

theorem no_request (output) : output ∉ requests core occ := by
  intro member
  have old := (requests_iff occ output).mp member
  obtain ⟨x,seen,alias,some⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp old
  have converted : GeneralNominalSaturationState.Alias GeneralLiveCompoundLeafInstall316.after.core.erased.current
      child.identity x.occurrence.identity := owner_eq ▸ alias
  exact GeneralLiveCompoundAdmin316.leaf_requests raw_sites_after GeneralLiveCompoundPost316.aliases_after output
    (GeneralNominalCenteredHeadOutputs.mem_requests_iff.mpr ⟨x,seen,converted,some⟩)

theorem equal_outputs (m : Assignment) (focus : Occurrence roles) : EqualOutputs core focus m := by
  intro a first b last _
  cases GeneralLiveCompoundAdmin316.all_requests raw_sites_after ((requests_iff focus a).mp first)
  cases GeneralLiveCompoundAdmin316.all_requests raw_sites_after ((requests_iff focus b).mp last)
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem classes (m : Assignment) : GeneralNominalVersionedEffects231.ClassEffects core occ plan m :=
  ⟨by intro out h; exact False.elim (no_request out h),equal_outputs m occ⟩

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready core occ plan :=
  fun out h => False.elim (no_request out h)

end Yulang.GeneralWhereVersionLeafRegistry317
