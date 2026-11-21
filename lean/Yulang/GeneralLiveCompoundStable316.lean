import Yulang.GeneralLiveCompoundPostFrames316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 38000000
namespace Yulang.GeneralLiveCompoundStable316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry)
open GeneralLiveCompoundLeafInstall316 (after reachable)
open GeneralLiveCompoundChildSite316 (childSite child)
open GeneralLiveCompoundPost316 (raw_sites_after centers_after point_closed)
open GeneralLiveCompoundPostFrames316
open GeneralLiveCompoundPostFeedback316 (no_refresh closed)
open GeneralNominalVersionedMixedKernel234 (Stable Step)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalSaturationState (Generated)

theorem reached_cases {focus : GeneralSourceDictionaries.Occurrence roles}
    (reached : Generated after.core.erased.current root focus) :
    focus = root ∨ focus = child := by
  obtain ⟨site,present,eq⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
    (GeneralNominalVersionedMixedTrace235.reachable reachable).1 reached
  rw [raw_sites_after] at present
  rcases List.mem_cons.mp present with rfl | last
  · exact Or.inl eq.symm
  · cases List.mem_singleton.mp last
    exact Or.inr eq.symm

theorem halted (next : State roles) : ¬ Step registry root after next := by
  rintro ⟨focus,path,step⟩
  have found := reached_cases path
  cases step with
  | administrative op =>
    cases op with
    | enqueue linked absent =>
      rcases found with rfl|rfl
      · exact absent _ (raw_sites_after ▸ List.mem_cons_self ..) rfl
      · exact absent _ (raw_sites_after ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _)) rfl
    | refresh ctx cert index present unknown known => exact no_refresh ctx cert index present unknown known
    | equate first last a b eq novel => exact novel (closed first last a b eq)
    | reobserve rev _ improved =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision point_closed rev improved
  | refresh atFocus ctx cert index present unknown known => exact no_refresh ctx cert index present unknown known
  | install e enabled novel =>
    have frame := e.frame
    rw [enabled.registry_eq,enabled.snapshot_eq] at frame
    rcases found with atRoot|atLeaf
    · rw [atRoot] at frame
      obtain ⟨model,before,packet,_⟩ := enabled.common
      exact no_root_packet before (by simpa only [root_frame_plan frame] using packet)
    · rw [atLeaf] at frame
      exact novel (leaf_frame_plan frame ▸ leaf_committed)
  | merge first last firstMember lastMember equal novel =>
    rw [centers_after] at firstMember lastMember
    rcases List.mem_cons.mp firstMember with rfl|one <;>
      rcases List.mem_cons.mp lastMember with rfl|two
    · exact novel (.refl _)
    · cases List.mem_singleton.mp two
      have clash : (0:Nat) = 1 := equal.1
      cases clash
    · cases List.mem_singleton.mp one
      have clash : (1:Nat) = 0 := equal.1
      cases clash
    · cases List.mem_singleton.mp one
      cases List.mem_singleton.mp two
      exact novel (.refl _)

theorem stable : Stable registry after root :=
  (GeneralNominalVersionedMixedKernel234.closure halted).1

theorem leaf_stable : Stable registry after child :=
  (GeneralNominalVersionedMixedKernel234.closure halted).2 _ GeneralLiveCompoundPost316.generated_after

end Yulang.GeneralLiveCompoundStable316
