import Yulang.GeneralWhereOriginSuccessor318

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeJournalPrefix347
open GeneralWhereVersionInstall317 (Journal Models install installCore)
open GeneralNominalCandidates (Context)
open GeneralNominalCenters (Plan)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralNominalRefinements (Refines)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCenteredHeadStepEffects (requests_subset_of_sites_aliases)
open GeneralNominalVersionedFrameTransport232 (class_effects_iff)

theorem requests_kept (before : Journal rs) (ctx : Context) (p : Plan rs) (focus) :
    requests before.mixed.core focus ⊆ requests (install before ctx p).mixed.core focus := by
  apply requests_subset_of_sites_aliases
  · intro site mem; exact List.mem_append_left _ mem
  · intro pair mem; exact mem

/-- Removing the last isolated transaction restricts the *same*
model, with no silent-child assumption. Older writers and their
authored output equations are kept at the smaller request class. -/
theorem previous {before : Journal rs} {ctx : Context} {p : Plan rs}
    (grow : Refines (rawOf before) ctx.state)
    (m : Assignment) (post : Models (install before ctx p) m) :
    Models before m := by
  have native := post.1
  refine ⟨⟨⟨GeneralNominalRefinements.models grow m native.1.1,native.1.2.1,?_,?_,native.1.2.2.2.2.1,?_⟩,
    native.2.1,?_⟩,?_⟩
  · intro site listed; exact native.1.2.2.1 site (List.mem_append_left _ listed)
  · intro site listed; exact native.1.2.2.2.1 site (List.mem_append_left _ listed)
  · intro effect used
    have e := native.1.2.2.2.2.2 effect used
    exact ⟨e.1,GeneralNominalCenteredHeadMatEffects.restrict (requests_kept before ctx p _) e.2⟩
  · intro effect used
    have e := native.2.2 effect used
    exact ⟨e.1,GeneralNominalVersionedJournal232.live_restrict (requests_kept before ctx p _) e.2⟩
  · intro q used
    have old := post.2 q (List.mem_append_left _ used)
    have asLegacy := (GeneralNominalVersionedEffects231.class_effects_iff ..).mp old.2
    exact ⟨old.1,(GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
      (GeneralNominalCenteredHeadMatEffects.restrict (requests_kept before ctx p _) asLegacy)⟩

end Yulang.GeneralDeclarativeJournalPrefix347
