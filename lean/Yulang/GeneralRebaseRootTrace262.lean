import Yulang.GeneralRebaseExecutableSnapshot262

namespace Yulang.GeneralRebaseRootTrace262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseSourceSnapshot261 (candidates)
open GeneralRebaseExecutableSnapshot262 (observe)

/-- An actual selected root is retained at its own intermediate state.
This is a proof witness, not an additional runtime journal. -/
inductive Trace (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat)
 (roots : State (GeneralRebaseStableClass261.facts plan owner (candidates source)) → List (Occurrence roles)) :
 List (Occurrence roles) → State (GeneralRebaseStableClass261.facts plan owner (candidates source)) →
 State (GeneralRebaseStableClass261.facts plan owner (candidates source)) → Prop where
 | nil (state) : Trace source plan owner roots [] state state
 | next {root rest before middle after} : root ∈ roots before →
   middle = write before (GeneralRebaseStableClass261.facts plan owner
     (GeneralRebaseExecutableRequests262.requests source root)) →
   middle.remaining ≠ before.remaining → Trace source plan owner roots rest middle after →
   Trace source plan owner roots (root :: rest) before after

theorem from_runs (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat) (roots)
 {n before after} (run : GeneralRebaseBudget258.Runs (observe source plan owner roots) n before after) :
 ∃ history, history.length = n ∧ Trace source plan owner roots history before after := by
 induction run with
 | nil state => exact ⟨[],rfl,.nil state⟩
 | next step _ ih =>
   obtain ⟨proposal,member,same,progress⟩ := step
   obtain ⟨outputs,included,rfl⟩ := List.mem_map.mp member
   obtain ⟨root,selected,rfl⟩ := List.mem_map.mp included
   obtain ⟨rest,length,trace⟩ := ih
   exact ⟨root :: rest,by simp [length],.next selected same progress trace⟩

theorem to_runs (source : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (owner : Nat) (roots)
 {history before after} (trace : Trace source plan owner roots history before after) :
 GeneralRebaseBudget258.Runs (observe source plan owner roots) history.length before after := by
 induction trace with
 | nil state => exact .nil state
 | next selected same progress _ ih =>
   exact .next ⟨_,List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨_,selected,rfl⟩,rfl⟩,same,progress⟩ ih

theorem models_exact (base : Assignment → Prop) (source : GeneralNominalCenteredSteps.State roles)
 (plan : Plan roles) (owner : Nat) (roots)
 {history before after} (trace : Trace source plan owner roots history before after) :
 ∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ root ∈ history, GeneralNominalVersionedEffects231.ClassEffects source root plan assignment := by
 induction trace with
 | nil state => intro assignment; simp
 | @next root rest before middle after _ same _ _ ih =>
   intro assignment
   rw [ih,same]
   have meaning := GeneralRebaseStableClass261.actual_write base plan owner source root
     (candidates source) (GeneralRebaseSourceSnapshot261.covered source root) before assignment
   rw [GeneralRebaseExecutableRequests262.requests_eq]
   rw [meaning]
   simp only [List.mem_cons,forall_eq_or_imp]
   exact and_assoc

/-- Finite completion with position-sensitive root provenance and exact
all-assignment effects. Neither model existence nor packet validity is concluded. -/
theorem certificate (base : Assignment → Prop) (source : GeneralNominalCenteredSteps.State roles)
 (plan : Plan roles) (owner : Nat) (roots)
 (before : State (GeneralRebaseStableClass261.facts plan owner (candidates source))) :
 ∃ after, ∃ history : List (Occurrence roles),
 GeneralRebaseSettle259.settle (observe source plan owner roots) before = .ok after ∧
 Trace source plan owner roots history before after ∧ history.length ≤ before.remaining.length ∧
 (∀ next, ¬ Step (observe source plan owner roots) after next) ∧
 (∀ assignment, GeneralRebaseStableClass261.Models base plan owner after assignment ↔
 GeneralRebaseStableClass261.Models base plan owner before assignment ∧
 ∀ root ∈ history, GeneralNominalVersionedEffects231.ClassEffects source root plan assignment) := by
 obtain ⟨after,n,success,run,bound,terminal⟩ := GeneralRebaseExecutableSnapshot262.completion source plan owner roots before
 obtain ⟨history,length,trace⟩ := from_runs source plan owner roots run
 exact ⟨after,history,success,trace,by simpa [length] using bound,terminal,
   models_exact base source plan owner roots trace⟩
end Yulang.GeneralRebaseRootTrace262
