import Yulang.GeneralRebaseDynamicSource262

namespace Yulang.GeneralRebaseSourceObserver262
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

/-- Source formation supplies the finite request pool. The observer is still
an explicit input and must return snapshots reachable from this same source.
This is not a construction or simulation of a complete source compiler. -/
theorem source_observer (sourceRegistry : Registry) (root : Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ pool : List Output, ∀ (plan : Plan roles) (owner : Nat)
 (inspect : State (GeneralRebaseStableClass261.facts plan owner pool) → GeneralNominalVersionedJournal232.State roles)
 (roots : State (GeneralRebaseStableClass261.facts plan owner pool) → List (Occurrence roles)),
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root)
   start (inspect state)) →
 ∀ before, ∃ after steps,
 GeneralRebaseSettle259.settle (GeneralRebaseDynamicSource262.observe plan owner pool
   (fun state => (inspect state).core) roots) before = .ok after ∧
 GeneralRebaseBudget258.Runs (GeneralRebaseDynamicSource262.observe plan owner pool
   (fun state => (inspect state).core) roots) steps before after ∧
 steps ≤ before.remaining.length ∧
 (∀ next, ¬ Step (GeneralRebaseDynamicSource262.observe plan owner pool
   (fun state => (inspect state).core) roots) after next) := by
 obtain ⟨pool,coverage⟩ := GeneralRebaseSourceRequestPool262.mixed_finite_requests sourceRegistry root start source
 refine ⟨pool,?_⟩
 intro plan owner inspect roots reachable before
 exact GeneralRebaseDynamicSource262.completion plan owner pool (fun state => (inspect state).core)
   roots (fun state => coverage (inspect state) (reachable state)) before

/-- The same source-derived pool works simultaneously for any assignment,
any fixed plan and every step of any reachable-snapshot observer. -/
theorem source_step_models (sourceRegistry : Registry) (root : Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ pool : List Output, ∀ (base : Assignment → Prop) (plan : Plan roles) (owner : Nat)
 (inspect : State (GeneralRebaseStableClass261.facts plan owner pool) → GeneralNominalVersionedJournal232.State roles)
 (roots : State (GeneralRebaseStableClass261.facts plan owner pool) → List (Occurrence roles)),
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root)
   start (inspect state)) →
 ∀ before after, Step (GeneralRebaseDynamicSource262.observe plan owner pool
   (fun state => (inspect state).core) roots) before after →
 ∃ chosen ∈ roots before, ∀ assignment,
 GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (inspect before).core chosen plan assignment := by
 obtain ⟨pool,coverage⟩ := GeneralRebaseSourceRequestPool262.mixed_finite_requests sourceRegistry root start source
 refine ⟨pool,?_⟩
 intro base plan owner inspect roots reachable before after step
 exact GeneralRebaseDynamicSource262.step_actual base plan owner pool (fun state => (inspect state).core)
   roots (fun state => coverage (inspect state) (reachable state)) before after step
end Yulang.GeneralRebaseSourceObserver262
