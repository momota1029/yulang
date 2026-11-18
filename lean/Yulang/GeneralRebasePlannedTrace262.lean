import Yulang.GeneralRebaseObservedPlan262

namespace Yulang.GeneralRebasePlannedTrace262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseObservedPlan262 (observe Compatible)

structure Event (roles : Roles.RoleDecls) where
 source : GeneralNominalCenteredSteps.State roles
 root : Occurrence roles
 plan : Plan roles

/-- Each event stores the exact snapshot and root observed at its intermediate
rebase state. This exists only as a proof witness of the compressed run. -/
inductive Trace (plan : Plan roles) (owner : Nat) (pool : List Output)
 (inspect : State (GeneralRebaseStableClass261.facts plan owner pool) → GeneralNominalCenteredSteps.State roles)
 (roots : State (GeneralRebaseStableClass261.facts plan owner pool) → List (Occurrence roles))
 (plans : State (GeneralRebaseStableClass261.facts plan owner pool) → Occurrence roles → Plan roles) :
 List (Event roles) → State (GeneralRebaseStableClass261.facts plan owner pool) →
 State (GeneralRebaseStableClass261.facts plan owner pool) → Prop where
 | nil (state) : Trace plan owner pool inspect roots plans [] state state
 | next {root rest before middle after} : root ∈ roots before →
   middle = write before (GeneralRebaseStableClass261.facts (plans before root) owner
     (GeneralRebaseExecutableRequests262.requests (inspect before) root)) →
   middle.remaining ≠ before.remaining → Trace plan owner pool inspect roots plans rest middle after →
   Trace plan owner pool inspect roots plans (⟨inspect before,root,plans before root⟩ :: rest) before after

theorem from_runs (plan : Plan roles) (owner : Nat) (pool : List Output) (inspect) (roots) (plans)
 {n before after} (run : GeneralRebaseBudget258.Runs (observe plan owner pool inspect roots plans) n before after) :
 ∃ history, history.length = n ∧ Trace plan owner pool inspect roots plans history before after := by
 induction run with
 | nil state => exact ⟨[],rfl,.nil state⟩
 | next step _ ih =>
   obtain ⟨proposal,member,same,progress⟩ := step
   obtain ⟨root,selected,rfl⟩ := List.mem_map.mp member
   obtain ⟨rest,length,trace⟩ := ih
   exact ⟨⟨_,root,_⟩ :: rest,by simp [length],.next selected same progress trace⟩

theorem to_runs (plan : Plan roles) (owner : Nat) (pool : List Output) (inspect) (roots) (plans)
 {history before after} (trace : Trace plan owner pool inspect roots plans history before after) :
 GeneralRebaseBudget258.Runs (observe plan owner pool inspect roots plans) history.length before after := by
 induction trace with
 | nil state => exact .nil state
 | next selected same progress _ ih =>
   exact .next ⟨_,List.mem_map.mpr ⟨_,selected,rfl⟩,same,progress⟩ ih

theorem models_exact (base : Assignment → Prop) (plan : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (compatible : Compatible plan owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 {history before after} (trace : Trace plan owner pool inspect roots plans history before after) :
 ∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.source event.root event.plan assignment := by
 induction trace with
 | nil state => intro assignment; simp
 | @next root rest before middle after selected same _ _ ih =>
   intro assignment
   rw [ih,same,GeneralRebaseObservedPlan262.write_eq plan owner pool inspect roots plans compatible before root selected]
   rw [GeneralRebaseExecutableRequests262.requests_eq]
   rw [GeneralRebaseStableClass261.actual_write base plan owner (inspect before) root pool
     (GeneralRebaseChildRequestPool262.requests_covered _ _ (coverage before) root) before assignment]
   simp only [List.mem_cons,forall_eq_or_imp]
   exact (and_congr (and_congr Iff.rfl (GeneralRebasePlanTransport262.class_effects plan (plans before root)
     (compatible before root selected) (inspect before) root assignment)) Iff.rfl).trans and_assoc

theorem certificate (base : Assignment → Prop) (plan : Plan roles) (owner : Nat) (pool : List Output)
 (inspect) (roots) (plans) (compatible : Compatible plan owner pool roots plans)
 (coverage : ∀ state, GeneralRebaseChildRequestPool262.Covered (inspect state) pool)
 (before : State (GeneralRebaseStableClass261.facts plan owner pool)) :
 ∃ after, ∃ history : List (Event roles),
 GeneralRebaseSettle259.settle (observe plan owner pool inspect roots plans) before = .ok after ∧
 Trace plan owner pool inspect roots plans history before after ∧ history.length ≤ before.remaining.length ∧
 (∀ next, ¬ Step (observe plan owner pool inspect roots plans) after next) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.source event.root event.plan assignment) := by
 obtain ⟨after,n,success,run,bound,terminal⟩ := GeneralRebaseObservedPlan262.completion plan owner pool inspect roots plans compatible coverage before
 obtain ⟨history,length,trace⟩ := from_runs plan owner pool inspect roots plans run
 exact ⟨after,history,success,trace,by simpa [length] using bound,terminal,
   models_exact base plan owner pool inspect roots plans compatible coverage trace⟩

/-- One pool is derived from source formation before choosing any observer or
Plan schedule. Each inspected snapshot must be source-reachable and each
selected Plan structurally compatible with the fixed reference Plan. -/
theorem source_certificate (sourceRegistry : GeneralDeclarations.Registry) (root : Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ pool : List Output, ∀ (base : Assignment → Prop) (fixed : Plan roles) (owner : Nat)
 (inspect : State (GeneralRebaseStableClass261.facts fixed owner pool) → GeneralNominalVersionedJournal232.State roles)
 (roots : State (GeneralRebaseStableClass261.facts fixed owner pool) → List (Occurrence roles))
 (plans : State (GeneralRebaseStableClass261.facts fixed owner pool) → Occurrence roles → Plan roles),
 Compatible fixed owner pool roots plans →
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root)
   start (inspect state)) →
 ∀ before, ∃ after, ∃ history : List (Event roles),
 GeneralRebaseSettle259.settle (observe fixed owner pool (fun state => (inspect state).core) roots plans) before = .ok after ∧
 Trace fixed owner pool (fun state => (inspect state).core) roots plans history before after ∧
 history.length ≤ before.remaining.length ∧
 (∀ next, ¬ Step (observe fixed owner pool (fun state => (inspect state).core) roots plans) after next) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base fixed owner after assignment ↔
 GeneralRebaseStableClass261.Models base fixed owner before assignment ∧
 ∀ event ∈ history, GeneralNominalVersionedEffects231.ClassEffects event.source event.root event.plan assignment) := by
 obtain ⟨pool,coverage⟩ := GeneralRebaseSourceRequestPool262.mixed_finite_requests sourceRegistry root start source
 refine ⟨pool,?_⟩
 intro base fixed owner inspect roots plans compatible reachable before
 exact certificate base fixed owner pool (fun state => (inspect state).core) roots plans compatible
   (fun state => coverage (inspect state) (reachable state)) before
end Yulang.GeneralRebasePlannedTrace262
