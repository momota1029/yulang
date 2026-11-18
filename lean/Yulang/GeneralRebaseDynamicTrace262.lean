import Yulang.GeneralRebaseSourceObserver262

namespace Yulang.GeneralRebaseDynamicTrace262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseDynamicSource262 (observe)

abbrev Event (roles : Roles.RoleDecls) := GeneralNominalCenteredSteps.State roles × Occurrence roles

/-- Each event stores the exact snapshot and root observed at its intermediate
rebase state. This exists only as a proof witness of the compressed run. -/
inductive Trace (plan : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : State (GeneralRebaseStableClass261.facts plan owner pool) → GeneralNominalCenteredSteps.State roles)
 (roots : State (GeneralRebaseStableClass261.facts plan owner pool) → List (Occurrence roles)) :
 List (Event roles) → State (GeneralRebaseStableClass261.facts plan owner pool) →
 State (GeneralRebaseStableClass261.facts plan owner pool) → Prop where
 | nil (state) : Trace plan owner pool inspect roots [] state state
 | next {root rest before middle after} : root ∈ roots before →
   middle = write before (GeneralRebaseStableClass261.facts plan owner
     (GeneralRebaseExecutableRequests262.requests (inspect before) root)) →
   middle.remaining ≠ before.remaining → Trace plan owner pool inspect roots rest middle after →
   Trace plan owner pool inspect roots ((inspect before,root) :: rest) before after

theorem from_runs (plan : Plan roles) (owner : Nat) (pool : List Output) (inspect) (roots)
 {n before after} (run : GeneralRebaseBudget258.Runs (observe plan owner pool inspect roots) n before after) :
 ∃ history, history.length = n ∧ Trace plan owner pool inspect roots history before after := by
 induction run with
 | nil state => exact ⟨[],rfl,.nil state⟩
 | next step _ ih =>
   obtain ⟨proposal,member,same,progress⟩ := step
   obtain ⟨outputs,included,rfl⟩ := List.mem_map.mp member
   obtain ⟨root,selected,rfl⟩ := List.mem_map.mp included
   obtain ⟨rest,length,trace⟩ := ih
   exact ⟨(_,root) :: rest,by simp [length],.next selected same progress trace⟩

theorem to_runs (plan : Plan roles) (owner : Nat) (pool : List Output) (inspect) (roots)
 {history before after} (trace : Trace plan owner pool inspect roots history before after) :
 GeneralRebaseBudget258.Runs (observe plan owner pool inspect roots) history.length before after := by
 induction trace with
 | nil state => exact .nil state
 | next selected same progress _ ih =>
   exact .next ⟨_,List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨_,selected,rfl⟩,rfl⟩,same,progress⟩ ih

theorem models_exact (base : Assignment → Prop) (plan : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 {history before after} (trace : Trace plan owner pool inspect roots history before after) :
 ∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.1 event.2 plan assignment := by
 induction trace with
 | nil state => intro assignment; simp
 | @next root rest before middle after _ same _ _ ih =>
   intro assignment
   rw [ih,same]
   rw [GeneralRebaseExecutableRequests262.requests_eq]
   rw [GeneralRebaseStableClass261.actual_write base plan owner (inspect before) root pool
     (GeneralRebaseChildRequestPool262.requests_covered _ _ (coverage before) root) before assignment]
   simp only [List.mem_cons,forall_eq_or_imp]
   exact and_assoc

theorem certificate (base : Assignment → Prop) (plan : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : State (GeneralRebaseStableClass261.facts plan owner pool)) :
 ∃ after, ∃ history : List (Event roles),
 GeneralRebaseSettle259.settle (observe plan owner pool inspect roots) before = .ok after ∧
 Trace plan owner pool inspect roots history before after ∧ history.length ≤ before.remaining.length ∧
 (∀ next, ¬ Step (observe plan owner pool inspect roots) after next) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.1 event.2 plan assignment) := by
 obtain ⟨after,n,success,run,bound,terminal⟩ := GeneralRebaseDynamicSource262.completion plan owner pool inspect roots coverage before
 obtain ⟨history,length,trace⟩ := from_runs plan owner pool inspect roots run
 exact ⟨after,history,success,trace,by simpa [length] using bound,terminal,
   models_exact base plan owner pool inspect roots coverage trace⟩

/-- Source initial formation discharges the pool premise. Reachable snapshot
selection and one fixed Plan remain explicit; no old-Step simulation is claimed. -/
theorem source_certificate (sourceRegistry : GeneralDeclarations.Registry) (root : Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ pool : List Output, ∀ (base : Assignment → Prop) (plan : Plan roles) (owner : Nat)
 (inspect : State (GeneralRebaseStableClass261.facts plan owner pool) → GeneralNominalVersionedJournal232.State roles)
 (roots : State (GeneralRebaseStableClass261.facts plan owner pool) → List (Occurrence roles)),
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root)
   start (inspect state)) →
 ∀ before, ∃ after, ∃ history : List (Event roles),
 GeneralRebaseSettle259.settle (observe plan owner pool (fun state => (inspect state).core) roots) before = .ok after ∧
 Trace plan owner pool (fun state => (inspect state).core) roots history before after ∧
 history.length ≤ before.remaining.length ∧
 (∀ next, ¬ Step (observe plan owner pool (fun state => (inspect state).core) roots) after next) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.1 event.2 plan assignment) := by
 obtain ⟨pool,coverage⟩ := GeneralRebaseSourceRequestPool262.mixed_finite_requests sourceRegistry root start source
 refine ⟨pool,?_⟩
 intro base plan owner inspect roots reachable before
 exact certificate base plan owner pool (fun state => (inspect state).core) roots
   (fun state => coverage (inspect state) (reachable state)) before
end Yulang.GeneralRebaseDynamicTrace262
