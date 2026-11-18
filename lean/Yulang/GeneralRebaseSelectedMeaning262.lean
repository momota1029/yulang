import Yulang.GeneralRebaseSelectedSettle262
import Yulang.GeneralRebasePlannedTrace262

namespace Yulang.GeneralRebaseSelectedMeaning262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralRebaseSelectedSettle262 (Current)
open GeneralRebaseObservedPlan262 (observe Compatible)
open GeneralNominalCommonBridge (Assignment)

/-- The event history is extracted from the same checked intermediate states,
not from an unrelated run. Readiness therefore belongs to each exact event. -/
theorem from_checked (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) {states before after}
 (checked : GeneralRebaseSelectedSettle262.Trace fixed owner pool inspect roots plans states before after) :
 ∃ events : List (GeneralRebasePlannedTrace262.Event roles),
 events.length = states.length ∧
 GeneralRebasePlannedTrace262.Trace fixed owner pool inspect roots plans events before after ∧
 ∀ event ∈ events, GeneralNominalCenteredHeadMatEffects.Ready event.source event.root event.plan := by
 induction checked with
 | done => exact ⟨[],rfl,.nil _,by simp⟩
 | @next before middle final history ready advanced _ ih =>
   have step := GeneralRebaseScheduler259.next_step _ before middle advanced
   obtain ⟨proposal,member,same,progress⟩ := step
   obtain ⟨root,selected,rfl⟩ := List.mem_map.mp member
   obtain ⟨events,length,trace,readyEvents⟩ := ih
   refine ⟨⟨inspect before,root,plans before root⟩ :: events,by simp [length],
     .next selected same progress trace,?_⟩
   intro event member
   rcases List.mem_cons.mp member with rfl | member
   · exact (GeneralRebaseSelectedCheck262.actual_ready ..).mp ready root selected
   · exact readyEvents event member

/-- Successful checked execution, not an all-state readiness assumption,
supplies all visited-round and terminal readiness. Model meaning still requires
source-request coverage and structural Plan compatibility. -/
theorem certificate (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (compatible : Compatible fixed owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before after : Current fixed owner pool)
 (success : GeneralRebaseSelectedSettle262.run fixed owner pool inspect roots plans before = .ok after) :
 ∃ states, ∃ events : List (GeneralRebasePlannedTrace262.Event roles),
 GeneralRebaseSelectedSettle262.Trace fixed owner pool inspect roots plans states before after ∧
 GeneralRebasePlannedTrace262.Trace fixed owner pool inspect roots plans events before after ∧
 events.length = states.length ∧ events.length ≤ before.remaining.length ∧
 (∀ state ∈ states, GeneralRebaseSelectedCheck262.ReadyRoots (inspect state) (plans state) (roots state)) ∧
 GeneralRebaseSelectedCheck262.ReadyRoots (inspect after) (plans after) (roots after) ∧
 (∀ event ∈ events, GeneralNominalCenteredHeadMatEffects.Ready event.source event.root event.plan) ∧
 (∀ next, ¬ Step (observe fixed owner pool inspect roots plans) after next) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base fixed owner after assignment ↔
 GeneralRebaseStableClass261.Models base fixed owner before assignment ∧
 ∀ event ∈ events, GeneralNominalVersionedEffects231.ClassEffects event.source event.root event.plan assignment) := by
 obtain ⟨states,checked,_,bound,readyStates,readyFinal,terminal⟩ :=
   GeneralRebaseSelectedSettle262.certificate fixed owner pool inspect roots plans before after success
 obtain ⟨events,length,trace,readyEvents⟩ := from_checked fixed owner pool inspect roots plans checked
 exact ⟨states,events,checked,trace,length,by simpa [length] using bound,readyStates,readyFinal,readyEvents,terminal,
   GeneralRebasePlannedTrace262.models_exact base fixed owner pool inspect roots plans compatible coverage trace⟩

/-- Actual source formation derives one finite pool. Reachability and structural
Plan compatibility remain explicit, while visited-round readiness comes from
successful execution of the selected-only checker, not from a global premise. -/
theorem source_certificate (sourceRegistry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ pool : List Output, ∀ (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat)
 (inspect : Current fixed owner pool → GeneralNominalVersionedJournal232.State roles)
 (roots : Current fixed owner pool → List (GeneralSourceDictionaries.Occurrence roles))
 (plans : Current fixed owner pool → GeneralSourceDictionaries.Occurrence roles → Plan roles),
 Compatible fixed owner pool roots plans →
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root)
   start (inspect state)) →
 ∀ before after, GeneralRebaseSelectedSettle262.run fixed owner pool
   (fun state => (inspect state).core) roots plans before = .ok after →
 ∃ states, ∃ events : List (GeneralRebasePlannedTrace262.Event roles),
 GeneralRebaseSelectedSettle262.Trace fixed owner pool (fun state => (inspect state).core) roots plans states before after ∧
 GeneralRebasePlannedTrace262.Trace fixed owner pool (fun state => (inspect state).core) roots plans events before after ∧
 events.length = states.length ∧ events.length ≤ before.remaining.length ∧
 (∀ state ∈ states, GeneralRebaseSelectedCheck262.ReadyRoots (inspect state).core (plans state) (roots state)) ∧
 GeneralRebaseSelectedCheck262.ReadyRoots (inspect after).core (plans after) (roots after) ∧
 (∀ event ∈ events, GeneralNominalCenteredHeadMatEffects.Ready event.source event.root event.plan) ∧
 (∀ next, ¬ Step (observe fixed owner pool (fun state => (inspect state).core) roots plans) after next) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base fixed owner after assignment ↔
 GeneralRebaseStableClass261.Models base fixed owner before assignment ∧
 ∀ event ∈ events, GeneralNominalVersionedEffects231.ClassEffects event.source event.root event.plan assignment) := by
 obtain ⟨pool,coverage⟩ := GeneralRebaseSourceRequestPool262.mixed_finite_requests sourceRegistry root start source
 refine ⟨pool,?_⟩
 intro base fixed owner inspect roots plans compatible reachable before after success
 exact certificate base fixed owner pool (fun state => (inspect state).core) roots plans compatible
   (fun state => coverage (inspect state) (reachable state)) before after success
end Yulang.GeneralRebaseSelectedMeaning262
