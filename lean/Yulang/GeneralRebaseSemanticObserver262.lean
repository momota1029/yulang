import Yulang.GeneralRebasePlanSemantic262
import Yulang.GeneralRebaseObservedPlan262

namespace Yulang.GeneralRebaseSemanticObserver262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseObservedPlan262 (observe)

/-- Selected plans share only declaration and compilation layout. This is
sufficient for the finite proposal table, not for its semantic meaning. -/
def LayoutCompatible (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (roots : State (GeneralRebaseStableClass261.facts fixed owner pool) → List (Occurrence roles))
 (plans : State (GeneralRebaseStableClass261.facts fixed owner pool) → Occurrence roles → Plan roles) : Prop :=
 ∀ state root, root ∈ roots state → GeneralRebasePlanSemantic262.Layout fixed (plans state root)

/-- Under the unchanged base predicate, actual binder and default-center values
must agree semantically. Neither output-effect equivalence nor a source compiler
is supplied as a premise. Deriving this from real source models is separate. -/
def BaseCompatible (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (roots : State (GeneralRebaseStableClass261.facts fixed owner pool) → List (Occurrence roles))
 (plans : State (GeneralRebaseStableClass261.facts fixed owner pool) → Occurrence roles → Plan roles) : Prop :=
 ∀ state root, root ∈ roots state → ∀ assignment, base assignment →
 GeneralRebasePlanSemantic262.Compatible fixed (plans state root) assignment

theorem of_structural (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (roots) (plans) (compatible : GeneralRebaseObservedPlan262.Compatible fixed owner pool roots plans) :
 LayoutCompatible fixed owner pool roots plans ∧ BaseCompatible base fixed owner pool roots plans := by
 constructor
 · intro state root selected
   exact ⟨(compatible state root selected).declaration,(compatible state root selected).constructors,
     (compatible state root selected).interpretation⟩
 · intro state root selected assignment _
   exact GeneralRebasePlanSemantic262.of_structural fixed (plans state root) (compatible state root selected) assignment

theorem observe_eq (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (compatible : LayoutCompatible fixed owner pool roots plans) :
 observe fixed owner pool inspect roots plans = GeneralRebaseDynamicSource262.observe fixed owner pool inspect roots := by
 funext state
 unfold observe GeneralRebaseDynamicSource262.observe GeneralRebaseCandidateDriver261.observe
   GeneralRebaseDynamicSource262.select
 rw [List.map_map]
 apply List.map_congr_left
 intro root selected
 exact (GeneralRebasePlanSemantic262.facts_eq fixed (plans state root)
   (compatible state root selected) owner _).symm

theorem write_eq (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : State (GeneralRebaseStableClass261.facts fixed owner pool) → GeneralNominalCenteredSteps.State roles)
 (roots) (plans) (compatible : LayoutCompatible fixed owner pool roots plans)
 (before : State (GeneralRebaseStableClass261.facts fixed owner pool))
 (root : Occurrence roles) (selected : root ∈ roots before) :
 write before (GeneralRebaseStableClass261.facts (plans before root) owner
   (GeneralRebaseExecutableRequests262.requests (inspect before) root)) =
 write before (GeneralRebaseStableClass261.facts fixed owner
   (GeneralRebaseExecutableRequests262.requests (inspect before) root)) :=
 congrArg (write before) (GeneralRebasePlanSemantic262.facts_eq fixed (plans before root)
   (compatible before root selected) owner _).symm

theorem completion (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (compatible : LayoutCompatible fixed owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : State (GeneralRebaseStableClass261.facts fixed owner pool)) :
 ∃ after steps, GeneralRebaseSettle259.settle (observe fixed owner pool inspect roots plans) before = .ok after ∧
 GeneralRebaseBudget258.Runs (observe fixed owner pool inspect roots plans) steps before after ∧
 steps ≤ before.remaining.length ∧ (∀ next, ¬ Step (observe fixed owner pool inspect roots plans) after next) := by
 rw [observe_eq fixed owner pool inspect roots plans compatible]
 exact GeneralRebaseDynamicSource262.completion fixed owner pool inspect roots coverage before

/-- Model semantics includes base on both sides. Outside base both sides are
false, so no global assignment agreement is silently inferred. -/
theorem write_actual (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : State (GeneralRebaseStableClass261.facts fixed owner pool) → GeneralNominalCenteredSteps.State roles)
 (roots) (plans) (layout : LayoutCompatible fixed owner pool roots plans)
 (compatible : BaseCompatible base fixed owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : State (GeneralRebaseStableClass261.facts fixed owner pool))
 (root : Occurrence roles) (selected : root ∈ roots before) (assignment : Assignment) :
 GeneralRebaseStableClass261.Models base fixed owner
   (write before (GeneralRebaseStableClass261.facts (plans before root) owner
     (GeneralRebaseExecutableRequests262.requests (inspect before) root))) assignment ↔
 GeneralRebaseStableClass261.Models base fixed owner before assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (inspect before) root (plans before root) assignment := by
 rw [write_eq fixed owner pool inspect roots plans layout before root selected,
   GeneralRebaseExecutableRequests262.requests_eq,
   GeneralRebaseStableClass261.actual_write base fixed owner (inspect before) root pool
     (GeneralRebaseChildRequestPool262.requests_covered _ _ (coverage before) root) before assignment]
 constructor
 · rintro ⟨prior,effects⟩
   exact ⟨prior,(GeneralRebasePlanSemantic262.class_effects fixed (plans before root) assignment
     (compatible before root selected assignment prior.1) (inspect before) root).mp effects⟩
 · rintro ⟨prior,effects⟩
   exact ⟨prior,(GeneralRebasePlanSemantic262.class_effects fixed (plans before root) assignment
     (compatible before root selected assignment prior.1) (inspect before) root).mpr effects⟩

theorem step_actual (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : State (GeneralRebaseStableClass261.facts fixed owner pool) → GeneralNominalCenteredSteps.State roles)
 (roots) (plans) (layout : LayoutCompatible fixed owner pool roots plans)
 (compatible : BaseCompatible base fixed owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before after : State (GeneralRebaseStableClass261.facts fixed owner pool))
 (step : Step (observe fixed owner pool inspect roots plans) before after) :
 ∃ root ∈ roots before, ∀ assignment,
 GeneralRebaseStableClass261.Models base fixed owner after assignment ↔
 GeneralRebaseStableClass261.Models base fixed owner before assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (inspect before) root (plans before root) assignment := by
 obtain ⟨proposal,member,rfl,_⟩ := step
 obtain ⟨root,selected,rfl⟩ := List.mem_map.mp member
 exact ⟨root,selected,write_actual base fixed owner pool inspect roots plans layout compatible coverage before root selected⟩
end Yulang.GeneralRebaseSemanticObserver262
