import Yulang.GeneralRebaseLiveProjection264
import Yulang.GeneralRebaseSourceRequests264
namespace Yulang.GeneralRebaseSourceProjection264
open GeneralRebaseLiveProjection264
open GeneralRebaseSourceRequests264 (Growth Same)
open GeneralRebaseMultiSelection263 (ofPlan requests)
open GeneralSourceState (Output)

theorem growth_facts (before after : SourceState roles) (growth : Growth before after) :
 liveFacts before ⊆ liveFacts after := by
 apply monotone before.core after.core before.plans after.plans growth.plans
 intro plan _ output requested
 simpa only [requests,GeneralRebaseExecutableRequests262.requests_eq] using
   growth.requests (ofPlan plan).root output (by simpa only [requests,GeneralRebaseExecutableRequests262.requests_eq] using requested)

theorem same_facts (before after : SourceState roles) (same : Same before after) (fact : GeneralRebaseStep258.Fact) :
 fact ∈ liveFacts before ↔ fact ∈ liveFacts after := by
 apply same_members before.core after.core before.plans after.plans
 · intro plan; rw [same.plans]
 · intro plan _ output
   simpa only [requests,GeneralRebaseExecutableRequests262.requests_eq] using same.requests (ofPlan plan).root output

theorem same_projection (owners : List Nat) (pool : List Output) (before after : SourceState roles)
 (same : Same before after) : project owners pool before = project owners pool after :=
 project_same owners pool before after (same_facts before after same)

theorem step_square (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {before after : SourceState roles}
 (step : GeneralNominalVersionedMixedKernel234.Step registry root before after) :
 project owners pool after = GeneralRebaseStep258.write (project owners pool before) (liveFacts after) :=
 rescan owners pool before after (growth_facts before after (GeneralRebaseSourceRequests264.step_growth step))

theorem steps_square (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {before after : SourceState roles}
 (steps : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) before after) :
 project owners pool after = GeneralRebaseStep258.write (project owners pool before) (liveFacts after) :=
 rescan owners pool before after (growth_facts before after (GeneralRebaseSourceRequests264.steps_growth steps))

theorem step_rescan_batch (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {before after : SourceState roles}
 (step : GeneralNominalVersionedMixedKernel234.Step registry root before after) :
 project owners pool after = GeneralRebaseWriteAlgebra259.batch (project owners pool before)
   (after.plans.map fun plan => GeneralRebaseMultiSelection263.proposal after.core (ofPlan plan)) :=
 rescan_batch owners pool before after (growth_facts before after (GeneralRebaseSourceRequests264.step_growth step))

theorem refresh_stutters (owners : List Nat) (pool : List Output)
 (state : SourceState roles) (context : GeneralNominalCandidates.Context) :
 project owners pool state = project owners pool (GeneralNominalVersionedRefresh232.refresh state context) :=
 same_projection owners pool _ _ (GeneralRebaseSourceRequests264.refresh_same state context)

theorem reobserve_stutters (owners : List Nat) (pool : List Output)
 (state : SourceState roles) (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) :
 project owners pool state = project owners pool (GeneralNominalVersionedRefresh232.reobserve state revision) :=
 same_projection owners pool _ _ (GeneralRebaseSourceRequests264.reobserve_same state revision)

theorem equate_stutters (owners : List Nat) (pool : List Output)
 (state : SourceState roles) (first last : Nat) :
 project owners pool state = project owners pool (GeneralNominalVersionedAdministrative232.equate state first last) :=
 same_projection owners pool _ _ (GeneralRebaseSourceRequests264.equate_same state first last)

theorem merge_rescan (owners : List Nat) (pool : List Output)
 (state : SourceState roles) (first last : GeneralNominalCenters.Site roles) :
 project owners pool (GeneralNominalVersionedAdministrative232.merge state first last) =
 GeneralRebaseStep258.write (project owners pool state)
   (liveFacts (GeneralNominalVersionedAdministrative232.merge state first last)) :=
 rescan owners pool _ _ (growth_facts _ _ (GeneralRebaseSourceRequests264.merge_growth state first last))

/-- Only changed projections consume budget. This does not rule out infinitely
many source transitions whose finite projections are equal. -/
theorem strict_decrease (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {before after : SourceState roles}
 (step : GeneralNominalVersionedMixedKernel234.Step registry root before after)
 (changed : project owners pool after ≠ project owners pool before) :
 (project owners pool after).remaining.length < (project owners pool before).remaining.length := by
 have different : (project owners pool after).remaining ≠ (project owners pool before).remaining :=
   fun equal => changed (GeneralRebaseStep258.state_ext _ _ equal)
 rw [step_square owners pool step] at different ⊢
 exact GeneralRebaseStep258.filter_strict _ _ different
end Yulang.GeneralRebaseSourceProjection264
