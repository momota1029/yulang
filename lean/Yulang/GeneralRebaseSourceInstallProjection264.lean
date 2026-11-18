import Yulang.GeneralRebaseSourceRequests264
import Yulang.GeneralRebaseLiveProjection264
namespace Yulang.GeneralRebaseSourceInstallProjection264
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralRebaseStep258 (Fact write)
open GeneralRebaseLiveProjection264 (facts liveFacts project)
open GeneralRebaseMultiSelection263 (proposal ofPlan)
open GeneralSourceState (Output)

/-- Actual checked source installation preserves every historical Plan's
proposal membership. This uses source request conservation, not an arbitrary
assumption that a projection commutes. -/
theorem historical_facts (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (enabled : Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect)
 (fact : Fact) :
 fact ∈ facts (GeneralNominalVersionedInstall232.install state effect).core state.plans ↔
 fact ∈ liveFacts state := by
 apply GeneralRebaseLiveProjection264.same_members _ _ _ _ (fun _ => Iff.rfl)
 intro plan member output
 simpa only [GeneralRebaseMultiSelection263.requests,GeneralRebaseExecutableRequests262.requests_eq,ofPlan] using
   GeneralRebaseSourceRequests264.source_install_old_requests registry checked root state reachable effect enabled plan member output

/-- Only the new Plan proposal remains after historical request conservation.
This decomposition is NOT asserted for arbitrary, non-source installations. -/
theorem liveFacts_exact (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (enabled : Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect)
 (fact : Fact) :
 fact ∈ liveFacts (GeneralNominalVersionedInstall232.install state effect) ↔
 fact ∈ proposal (GeneralNominalVersionedInstall232.install state effect).core (ofPlan effect.plan) ∨
 fact ∈ liveFacts state := by
 change fact ∈ proposal _ (ofPlan effect.plan) ++ facts _ state.plans ↔ _
 rw [List.mem_append,historical_facts registry checked root state reachable effect enabled fact]

/-- Sharp source-to-finite installation square. It may stutter when the
proposal adds no new finite facts; no strict Step or inverse is asserted. -/
theorem project_install (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (enabled : Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect)
 (owners : List Nat) (pool : List Output) :
 project owners pool (GeneralNominalVersionedInstall232.install state effect) =
 write (project owners pool state)
   (proposal (GeneralNominalVersionedInstall232.install state effect).core (ofPlan effect.plan)) := by
 unfold project
 rw [← GeneralRebaseWriteAlgebra259.append]
 apply GeneralRebaseLiveProjection264.write_members
 intro fact
 rw [List.mem_append,liveFacts_exact registry checked root state reachable effect enabled fact]
 exact or_comm


/-- The prospective Plan's root is present by its actual Frame, even before
it has become a member of the versioned journal. -/
theorem current_requests (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (enabled : Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect)
 (output : Output) :
 output ∈ GeneralNominalCenteredHeadOutputs.requests (GeneralNominalVersionedInstall232.install state effect).core effect.plan.packet.site.occurrence ↔
 output ∈ GeneralNominalCenteredHeadOutputs.requests state.core effect.plan.packet.site.occurrence := by
 have frame := GeneralNominalVersionedMixedAncestry237.frame enabled
 exact GeneralNominalVersionedMixedCommon235.requests_iff checked reachable enabled.registry_eq enabled.snapshot_eq
   ⟨effect.plan.packet.site,frame.raw_recorded,rfl⟩

theorem current_proposal (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (enabled : Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect)
 (fact : Fact) :
 fact ∈ proposal (GeneralNominalVersionedInstall232.install state effect).core (ofPlan effect.plan) ↔
 fact ∈ proposal state.core (ofPlan effect.plan) := by
 have same : ∀ output,
   output ∈ GeneralRebaseMultiSelection263.requests (GeneralNominalVersionedInstall232.install state effect).core (ofPlan effect.plan) ↔
   output ∈ GeneralRebaseMultiSelection263.requests state.core (ofPlan effect.plan) := by
   intro output
   simpa only [GeneralRebaseMultiSelection263.requests,GeneralRebaseExecutableRequests262.requests_eq,ofPlan] using
     current_requests registry checked root state reachable effect enabled output
 constructor
 · exact GeneralRebaseStableClass261.monotone _ _ _ _ (fun output member => (same output).mp member) fact
 · exact GeneralRebaseStableClass261.monotone _ _ _ _ (fun output member => (same output).mpr member) fact

theorem project_install_current (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (enabled : Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect)
 (owners : List Nat) (pool : List Output) :
 project owners pool (GeneralNominalVersionedInstall232.install state effect) =
 write (project owners pool state) (proposal state.core (ofPlan effect.plan)) := by
 rw [project_install registry checked root state reachable effect enabled owners pool]
 exact GeneralRebaseLiveProjection264.write_members _ _ _ (current_proposal registry checked root state reachable effect enabled)
end Yulang.GeneralRebaseSourceInstallProjection264
