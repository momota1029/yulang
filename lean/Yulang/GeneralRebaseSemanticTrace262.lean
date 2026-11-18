import Yulang.GeneralRebaseSemanticObserver262
import Yulang.GeneralRebaseSelectedMeaning262

namespace Yulang.GeneralRebaseSemanticTrace262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebasePlannedTrace262 (Trace Event)
open GeneralRebaseSemanticObserver262 (LayoutCompatible BaseCompatible)
open GeneralRebaseObservedPlan262 (observe)

/-- Binder identities can change, provided their values agree under base.
The exact same actual Plan history works for every assignment. -/
theorem models_exact (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (layout : LayoutCompatible fixed owner pool roots plans)
 (compatible : BaseCompatible base fixed owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 {history before after} (trace : Trace fixed owner pool inspect roots plans history before after) :
 ∀ assignment, GeneralRebaseStableClass261.Models base fixed owner after assignment ↔
 GeneralRebaseStableClass261.Models base fixed owner before assignment ∧
 ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.source event.root event.plan assignment := by
 induction trace with
 | nil state => intro assignment; simp
 | @next root rest before middle after selected same _ _ ih =>
   intro assignment
   rw [ih,same,GeneralRebaseSemanticObserver262.write_actual base fixed owner pool inspect roots plans
     layout compatible coverage before root selected assignment]
   simp only [List.mem_cons,forall_eq_or_imp]
   exact and_assoc

/-- Success of the selected-only checker supplies readiness; it is not a
premise imposed on the whole finite pool or on unvisited rebase states. -/
theorem checked_certificate (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (layout : LayoutCompatible fixed owner pool roots plans)
 (compatible : BaseCompatible base fixed owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before after : State (GeneralRebaseStableClass261.facts fixed owner pool))
 (success : GeneralRebaseSelectedSettle262.run fixed owner pool inspect roots plans before = .ok after) :
 ∃ states, ∃ history : List (Event roles),
 GeneralRebaseSelectedSettle262.Trace fixed owner pool inspect roots plans states before after ∧
 Trace fixed owner pool inspect roots plans history before after ∧ history.length = states.length ∧
 history.length ≤ before.remaining.length ∧
 (∀ event ∈ history, GeneralNominalCenteredHeadMatEffects.Ready event.source event.root event.plan) ∧
 GeneralRebaseSelectedCheck262.ReadyRoots (inspect after) (plans after) (roots after) ∧
 (∀ next, ¬ Step (observe fixed owner pool inspect roots plans) after next) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base fixed owner after assignment ↔
 GeneralRebaseStableClass261.Models base fixed owner before assignment ∧
 ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.source event.root event.plan assignment) := by
 obtain ⟨states,checked,_,bound,_,readyFinal,terminal⟩ :=
   GeneralRebaseSelectedSettle262.certificate fixed owner pool inspect roots plans before after success
 obtain ⟨history,length,trace,ready⟩ := GeneralRebaseSelectedMeaning262.from_checked fixed owner pool inspect roots plans checked
 exact ⟨states,history,checked,trace,length,by simpa [length] using bound,ready,readyFinal,terminal,
   models_exact base fixed owner pool inspect roots plans layout compatible coverage trace⟩
/-- Actual source formation derives one finite pool. Reachability and base-relative
Plan compatibility remain explicit, while visited-round readiness comes from
successful execution of the selected-only checker, not from a global premise. -/
theorem source_certificate (sourceRegistry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ pool : List Output, ∀ (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat)
 (inspect : State (GeneralRebaseStableClass261.facts fixed owner pool) → GeneralNominalVersionedJournal232.State roles)
 (roots : State (GeneralRebaseStableClass261.facts fixed owner pool) → List (GeneralSourceDictionaries.Occurrence roles))
 (plans : State (GeneralRebaseStableClass261.facts fixed owner pool) → GeneralSourceDictionaries.Occurrence roles → Plan roles),
 LayoutCompatible fixed owner pool roots plans →
 BaseCompatible base fixed owner pool roots plans →
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root)
   start (inspect state)) →
 ∀ before after, GeneralRebaseSelectedSettle262.run fixed owner pool
   (fun state => (inspect state).core) roots plans before = .ok after →
 ∃ states, ∃ events : List (GeneralRebasePlannedTrace262.Event roles),
 GeneralRebaseSelectedSettle262.Trace fixed owner pool (fun state => (inspect state).core) roots plans states before after ∧
 GeneralRebasePlannedTrace262.Trace fixed owner pool (fun state => (inspect state).core) roots plans events before after ∧
 events.length = states.length ∧ events.length ≤ before.remaining.length ∧
 (∀ event ∈ events, GeneralNominalCenteredHeadMatEffects.Ready event.source event.root event.plan) ∧
 GeneralRebaseSelectedCheck262.ReadyRoots (inspect after).core (plans after) (roots after) ∧
 (∀ next, ¬ Step (observe fixed owner pool (fun state => (inspect state).core) roots plans) after next) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base fixed owner after assignment ↔
 GeneralRebaseStableClass261.Models base fixed owner before assignment ∧
 ∀ event ∈ events, GeneralNominalVersionedEffects231.ClassEffects event.source event.root event.plan assignment) := by
 obtain ⟨pool,coverage⟩ := GeneralRebaseSourceRequestPool262.mixed_finite_requests sourceRegistry root start source
 refine ⟨pool,?_⟩
 intro base fixed owner inspect roots plans layout compatible reachable before after success
 exact checked_certificate base fixed owner pool (fun state => (inspect state).core) roots plans layout compatible
   (fun state => coverage (inspect state) (reachable state)) before after success
end Yulang.GeneralRebaseSemanticTrace262
