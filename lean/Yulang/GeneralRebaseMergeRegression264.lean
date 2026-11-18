import Yulang.GeneralRebaseMergeRequests264
import Yulang.GeneralRebaseLiveProjection264
import Yulang.GeneralRebaseMergeRequests261
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseMergeRegression264
open GeneralNominalCenters GeneralRebaseStep258
open GeneralNominalCenteredHeadAllocMergeSource (roles registry root)
open GeneralNominalCenteredHeadAllocMergeInstall (installed aSite bSite aTarget bTarget)
open GeneralNominalCenteredHeadAllocMergeState (installed_sites installed_raw_sites generated_a not_aliased a_outputs b_outputs child_ids_distinct a_above_root)
open GeneralRebaseMultiSelection263 (ofPlan proposal)
open GeneralNominalSaturationState (Alias)
open GeneralSourceState (Output)

/-- An explicit versioned journal over actual premerge raw data. Its extra
candidate is supplied, so source reachability of this whole state is NOT claimed. -/
abbrev plan := GeneralRebaseMergeRequests261.candidate []
def sample : GeneralNominalVersionedJournal232.State roles := ⟨installed,[plan],[]⟩
def merged := GeneralNominalVersionedAdministrative232.merge sample aSite bSite
abbrev owner := (ofPlan plan).owner
abbrev first : Output := ⟨0,aTarget⟩
abbrev last : Output := ⟨0,bTarget⟩
abbrev pool := [first,last]
abbrev owners := [owner]
abbrev gained := GeneralRebasePairKeys261.key owner last last

/-- An actual MixedKernel Step with every merge guard, but not a claim that
the explicitly supplied sample journal arose from source initialization. -/
theorem merge_step : GeneralNominalVersionedMixedKernel234.Step registry root sample merged := by
 refine ⟨aSite.occurrence,generated_a,.merge aSite bSite ?_ ?_ ⟨rfl,.nil⟩ not_aliased⟩
 · change aSite ∈ installed.core.sites
   rw [installed_sites]; simp
 · change bSite ∈ installed.core.sites
   rw [installed_sites]; simp

private theorem old_alias_identity {a b : Nat} (same : Alias sample.core.erased.current a b) : a = b := by
 induction same with
 | refl => rfl
 | edge member => cases member
 | symm _ ih => exact ih.symm
 | trans _ _ one two => exact one.trans two

theorem last_absent : last ∉ GeneralNominalCenteredHeadOutputs.requests sample.core aSite.occurrence := by
 intro member
 obtain ⟨site,present,same,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
 change site ∈ installed.core.erased.current.sites at present
 rw [installed_raw_sites] at present
 rcases List.mem_cons.mp present with rfl | present
 · cases within
 · rcases List.mem_cons.mp present with rfl | present
   · change last ∈ aSite.occurrence.demand.outputs at within
     rw [a_outputs] at within
     exact GeneralNominalCenteredHeadAllocMergeInstall.targets_distinct
       (congrArg Output.target (List.mem_singleton.mp within)).symm
   · cases List.mem_singleton.mp present
     exact child_ids_distinct (old_alias_identity same)

theorem last_present : last ∈ GeneralNominalCenteredHeadOutputs.requests merged.core aSite.occurrence := by
 apply (GeneralRebaseMergeRequests264.requests_merge sample aSite bSite aSite.occurrence last).mpr
 refine Or.inr (Or.inl ⟨.refl _,?_⟩)
 exact GeneralNominalCenteredHeadOutputs.request_retained bSite.observed
   (by change bSite.observed ∈ installed.core.erased.current.sites; rw [installed_raw_sites]; simp)
   (.refl _) (by change last ∈ bSite.occurrence.demand.outputs; rw [b_outputs]; exact List.mem_singleton_self _)

theorem gained_before_absent : gained ∉ GeneralRebaseLiveProjection264.liveFacts sample := by
 intro member
 obtain ⟨candidate,present,fact⟩ := (GeneralRebaseLiveProjection264.member sample.core sample.plans gained).mp member
 cases List.mem_singleton.mp present
 rcases List.mem_append.mp fact with body | pair
 · obtain ⟨output,_,inside⟩ := (GeneralRebaseBodyTable261.member ..).mp body
   exact GeneralRebaseStableBody261.pair_outside plan owner last last output inside
 · obtain ⟨first,requested,last',_,_,same⟩ := (GeneralRebasePairKeys261.member ..).mp pair
   have equal := (GeneralRebasePairKeys261.key_injective same).2.1
   have requestedLast := equal ▸ requested
   exact last_absent (by simpa only [GeneralRebaseMultiSelection263.requests,GeneralRebaseExecutableRequests262.requests_eq,ofPlan,Site.observed] using requestedLast)

theorem gained_after : gained ∈ GeneralRebaseLiveProjection264.liveFacts merged := by
 apply (GeneralRebaseLiveProjection264.member merged.core merged.plans gained).mpr
 refine ⟨plan,List.mem_singleton_self _,List.mem_append_right _ ?_⟩
 have requested : last ∈ GeneralRebaseMultiSelection263.requests merged.core (ofPlan plan) := by
   simpa only [GeneralRebaseMultiSelection263.requests,GeneralRebaseExecutableRequests262.requests_eq,ofPlan,Site.observed] using last_present
 exact (GeneralRebasePairKeys261.member ..).mpr ⟨last,requested,last,requested,rfl,rfl⟩

theorem gained_basis : gained ∈ GeneralRebaseUniversalBasis263.basis owners pool := by
 apply List.mem_flatMap.mpr
 refine ⟨owner,List.mem_singleton_self _,List.mem_append_right _ ?_⟩
 exact (GeneralRebasePairKeys261.member ..).mpr
   ⟨last,List.mem_cons_of_mem _ (List.mem_singleton_self _),last,List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl,rfl⟩

theorem projection_changed : GeneralRebaseLiveProjection264.project owners pool merged ≠
 GeneralRebaseLiveProjection264.project owners pool sample := by
 intro equal
 have retained : gained ∈ (GeneralRebaseLiveProjection264.project owners pool sample).remaining := by
   apply List.mem_filter.mpr
   exact ⟨gained_basis,by simpa using gained_before_absent⟩
 have removed : gained ∉ (GeneralRebaseLiveProjection264.project owners pool merged).remaining := by
   intro present
   have absent : gained ∉ GeneralRebaseLiveProjection264.liveFacts merged := by
     simpa using (List.mem_filter.mp present).2
   exact absent gained_after
 exact removed (equal.symm ▸ retained)
theorem actual_strict_merge :
 GeneralNominalVersionedMixedKernel234.Step registry root sample merged ∧
 GeneralRebaseLiveProjection264.project owners pool merged ≠ GeneralRebaseLiveProjection264.project owners pool sample :=
 ⟨merge_step,projection_changed⟩
end Yulang.GeneralRebaseMergeRegression264
