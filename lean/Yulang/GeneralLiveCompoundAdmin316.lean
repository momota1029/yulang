import Yulang.GeneralLiveCompoundStaleRoot316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 24000000
namespace Yulang.GeneralLiveCompoundAdmin316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundChildSite316
open GeneralLiveCompoundUpperRefresh316 (upperState)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalSaturationState (Alias)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open CommonNominalFullCarrier

abbrev rootSite' := rootSite snapshot.seed root

theorem alias_eq {s : State roles} (none : s.core.erased.current.aliases = [])
    (same : Alias s.core.erased.current a b) : a = b := by
  induction same with
  | refl => rfl
  | edge present => rw [none] at present; cases present
  | symm _ ih => exact ih.symm
  | trans _ _ x y => exact x.trans y

theorem admin {s : State roles} (sites : s.core.sites = [rootSite',childSite])
    (which : focus = root ∨ focus = child) : AdministrativeReady s focus := by
  constructor
  · rcases which with rfl | rfl
    · exact ⟨rootSite',sites ▸ List.mem_cons_self,rfl⟩
    · exact ⟨childSite,sites ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl⟩
  · intro first one whereAt last two same
    rw [sites] at one two
    rcases List.mem_cons.mp one with rfl|one <;>
      rcases List.mem_cons.mp two with rfl|two
    · exact .refl _
    · cases List.mem_singleton.mp two
      have clash : (0:Nat) = 1 := same.1
      cases clash
    · cases List.mem_singleton.mp one
      have clash : (1:Nat) = 0 := same.1
      cases clash
    · cases List.mem_singleton.mp one
      cases List.mem_singleton.mp two
      exact .refl _

theorem all_requests {s : State roles}
    (sites : s.core.erased.current.sites =
      [GeneralNominalDemandMerging.pointSite root,childSite.observed])
    (member : output ∈ requests s.core focus) : output = ⟨0,4⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [sites] at present
  rcases List.mem_cons.mp present with same | present
  · subst site; exact List.mem_singleton.mp within
  · cases List.mem_singleton.mp present
    cases within

theorem equal_outputs {s : State roles} {w : GeneralNominalCommonBridge.Assignment}
    (sites : s.core.erased.current.sites =
      [GeneralNominalDemandMerging.pointSite root,childSite.observed]) :
    EqualOutputs s.core focus w := by
  intro first one last two _
  cases all_requests sites one
  cases all_requests sites two
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem leaf_requests {s : State roles}
    (sites : s.core.erased.current.sites =
      [GeneralNominalDemandMerging.pointSite root,childSite.observed])
    (none : s.core.erased.current.aliases = []) :
    ∀ output, output ∉ requests s.core child := by
  intro output member
  obtain ⟨site,present,aliases,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [sites] at present
  rcases List.mem_cons.mp present with one | two
  · subst site
    exact (by decide +kernel : child.identity ≠ root.identity) (alias_eq none aliases)
  · cases List.mem_singleton.mp two
    cases within

theorem leaf_classes {s : State roles} {w : GeneralNominalCommonBridge.Assignment}
    (sites : s.core.erased.current.sites =
      [GeneralNominalDemandMerging.pointSite root,childSite.observed])
    (none : s.core.erased.current.aliases = []) (plan : Plan roles) :
    GeneralNominalVersionedEffects231.ClassEffects s.core child plan w :=
  ⟨by intro o h; exact False.elim (leaf_requests sites none o h),equal_outputs sites⟩

end Yulang.GeneralLiveCompoundAdmin316
