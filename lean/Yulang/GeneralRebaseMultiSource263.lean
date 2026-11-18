import Yulang.GeneralRebaseRegisteredOwners263
import Yulang.GeneralRebaseMultiTrace263
import Yulang.GeneralRebaseSourceRequestPool262

namespace Yulang.GeneralRebaseMultiSource263
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseMultiSelection263 (Selection ofPlan)
open GeneralRebaseMultiObserver263
open GeneralRebaseOwnerTable263 (Models)

/-- These are the actual retained versioned Plans, not arbitrary roots or a
selector reading legacy core.plans. Historical plans may fail current readiness. -/
def selected (source : GeneralNominalVersionedJournal232.State roles) : List (Selection roles) :=
 source.plans.map ofPlan

theorem source_bounds (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start state →
 (∀ entry ∈ selected state, entry.owner ∈ owners) ∧ GeneralRebaseChildRequestPool262.Covered state.core pool := by
 obtain ⟨owners,ownerCovered⟩ := GeneralRebaseRegisteredOwners263.source_finite_codes registry root start source
 obtain ⟨pool,requestCovered⟩ := GeneralRebaseSourceRequestPool262.mixed_finite_requests registry root start source
 refine ⟨owners,pool,?_⟩
 intro state path
 refine ⟨?_,requestCovered state path⟩
 intro entry member
 obtain ⟨plan,registered,rfl⟩ := List.mem_map.mp member
 exact ownerCovered state path plan registered

/-- Source formation supplies both finite owner addresses and finite requests.
The inspector and representative Plans remain explicit inputs. Consecutive inspected
snapshots are not asserted to be consecutive old-source Steps. -/
theorem source_completion (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output, ∀ (representative : Nat → Plan roles)
 (inspect : Current owners representative pool → GeneralNominalVersionedJournal232.State roles),
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start (inspect state)) →
 LayoutCompatible owners representative pool (fun state => selected (inspect state)) →
 ∀ before, ∃ after steps,
 GeneralRebaseSettle259.settle (observe owners representative pool (fun state => (inspect state).core)
   (fun state => selected (inspect state))) before = .ok after ∧
 GeneralRebaseBudget258.Runs (observe owners representative pool (fun state => (inspect state).core)
   (fun state => selected (inspect state))) steps before after ∧
 steps ≤ owners.length * (pool.length + pool.length * pool.length) ∧
 (∀ next, ¬ Step (observe owners representative pool (fun state => (inspect state).core)
   (fun state => selected (inspect state))) after next) := by
 obtain ⟨owners,pool,bounds⟩ := source_bounds registry root start source
 refine ⟨owners,pool,?_⟩
 intro representative inspect reachable layout before
 exact completion owners representative pool (fun state => (inspect state).core) (fun state => selected (inspect state))
   (fun state => (bounds (inspect state) (reachable state)).1) layout
   (fun state => (bounds (inspect state) (reachable state)).2) before

theorem source_certificate (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output, ∀ (base : Assignment → Prop) (representative : Nat → Plan roles)
 (inspect : Current owners representative pool → GeneralNominalVersionedJournal232.State roles),
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start (inspect state)) →
 LayoutCompatible owners representative pool (fun state => selected (inspect state)) →
 BaseCompatible base owners representative pool (fun state => selected (inspect state)) →
 ∀ before after, GeneralRebaseMultiRun263.run owners representative pool (fun state => (inspect state).core)
   (fun state => selected (inspect state)) before = .ok after →
 ∃ events : List (GeneralRebaseMultiTrace263.Event roles),
 GeneralRebaseMultiTrace263.Trace owners representative pool (fun state => (inspect state).core)
   (fun state => selected (inspect state)) events before after ∧
 events.length ≤ owners.length * (pool.length + pool.length * pool.length) ∧
 (∀ event ∈ events, GeneralNominalCenteredHeadMatEffects.Ready event.source event.selected.root event.selected.plan) ∧
 GeneralRebaseMultiSelection263.Ready (inspect after).core (selected (inspect after)) ∧
 (∀ next, ¬ Step (observe owners representative pool (fun state => (inspect state).core)
   (fun state => selected (inspect state))) after next) ∧
 (∀ assignment, Models base owners representative after assignment ↔ Models base owners representative before assignment ∧
   ∀ event ∈ events, GeneralNominalVersionedEffects231.ClassEffects event.source event.selected.root event.selected.plan assignment) := by
 obtain ⟨owners,pool,bounds⟩ := source_bounds registry root start source
 refine ⟨owners,pool,?_⟩
 intro base representative inspect reachable layout compatible before after success
 obtain ⟨_,events,_,trace,_,bound,ready,final,terminal,meaning⟩ := GeneralRebaseMultiTrace263.certificate
   base owners representative pool (fun state => (inspect state).core) (fun state => selected (inspect state))
   (fun state => (bounds (inspect state) (reachable state)).1) layout compatible
   (fun state => (bounds (inspect state) (reachable state)).2) before after success
 exact ⟨events,trace,bound,ready,final,terminal,meaning⟩
end Yulang.GeneralRebaseMultiSource263
