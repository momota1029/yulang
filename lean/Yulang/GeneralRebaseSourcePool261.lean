import Yulang.GeneralRebaseSourceSnapshot261
import Yulang.GeneralNominalVersionedMixedInstallRequests235
namespace Yulang.GeneralRebaseSourcePool261
open GeneralNominalCenters
open GeneralRebaseSourceSnapshot261 (candidates)

theorem same_sites (before after : GeneralNominalCenteredSteps.State roles)
 (same : before.erased.current.sites = after.erased.current.sites) : candidates before = candidates after := by
 unfold candidates
 rw [same]

theorem merge_pool (state : GeneralNominalCenteredSteps.State roles) (first last : Site roles) (support) :
 candidates (GeneralNominalCenteredSteps.merge state first last support) = candidates state := rfl

theorem refresh_pool (state : GeneralNominalCenteredSteps.State roles) (context) :
 candidates (GeneralNominalCenteredSteps.refresh state context) = candidates state := rfl

/-- The existing Absorbed premise is sufficient for retaining the same request
pool under actual versioned installation. It is not silently assumed for
arbitrary new children with new output targets. List multiplicity may grow. -/
theorem absorbed_install (state : GeneralNominalVersionedJournal232.State roles) (plan : Plan roles)
 (absorbed : GeneralNominalVersionedMixedInstallRequests235.Absorbed state plan)
 (output : GeneralSourceState.Output) :
 output ∈ candidates (GeneralNominalVersionedInstall232.installCore state.core plan) ↔
 output ∈ candidates state.core := by
 constructor
 · intro included
   obtain ⟨site,member,within⟩ := List.mem_flatMap.mp included
   rcases List.mem_append.mp member with old | added
   · exact List.mem_flatMap.mpr ⟨site,old,within⟩
   · exact GeneralRebaseSourceSnapshot261.covered state.core site.occurrence output
       (absorbed site added output within)
 · intro included
   obtain ⟨site,member,within⟩ := List.mem_flatMap.mp included
   exact List.mem_flatMap.mpr ⟨site,List.mem_append_left _ member,within⟩

theorem installed_requests_covered (state : GeneralNominalVersionedJournal232.State roles) (plan : Plan roles)
 (absorbed : GeneralNominalVersionedMixedInstallRequests235.Absorbed state plan)
 (root : GeneralSourceDictionaries.Occurrence roles) :
 ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests (GeneralNominalVersionedInstall232.installCore state.core plan) root,
 output ∈ candidates state.core := by
 intro output included
 exact (absorbed_install state plan absorbed output).mp
   (GeneralRebaseSourceSnapshot261.covered _ root output included)
end Yulang.GeneralRebaseSourcePool261
