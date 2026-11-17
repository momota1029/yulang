import Yulang.GeneralPresenceUsedSupport245
import Yulang.GeneralPresenceOwnerTableCheck244
namespace Yulang.GeneralPresenceUsedTable245
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244 GeneralPresenceOwnerTable244
open GeneralPresenceUsedSupport245
variable {Name Owner : Type} [DecidableEq Name] [DecidableEq Owner]

/-- Boundary representation check, not a language acceptance test. -/
def retainedCheck (removed retained : List (Entry Name)) : Bool :=
 GeneralPresenceOwnerCheck244.disjointCheck removed retained &&
 crossCheck retained retained && activeCheck removed retained

theorem retained_exact (removed retained : List (Entry Name)) :
 retainedCheck removed retained = true ↔
 (DisjointTargets removed retained ∧ External retained) ∧ ActiveCrossRead removed retained := by
 simp only [retainedCheck,Bool.and_eq_true,GeneralPresenceOwnerCheck244.disjointCheck_exact,
   crossCheck_exact,activeCheck_exact,External]

def check (state : State Name Owner) (owner : Owner) : Bool :=
 state.owners.all fun other => if other = owner then true else retainedCheck (state.entries owner) (state.entries other)

theorem check_exact (state : State Name Owner) (owner : Owner) :
 check state owner = true ↔
 ∀ other ∈ state.owners, other ≠ owner → retainedCheck (state.entries owner) (state.entries other) = true := by
 unfold check
 constructor
 · intro valid other member different
   simpa [different] using List.all_eq_true.mp valid other member
 · intro valid
   apply List.all_eq_true.mpr
   intro other member
   by_cases same : other = owner
   · simp [same]
   · simpa [same] using valid other member same

theorem checked_models (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (present : owner ∈ state.owners) (checked : check state owner = true)
 (model : Model) (assignment : Name → Comp model) :
 Models (rebase state owner fresh) model assignment ↔
 PresenceNormalForm.All model assignment (block fresh) ∧ Consumers state owner model
   (fun name => (substitution (state.entries owner) name).eval model assignment) := by
 apply models_exact state owner fresh present
 intro other member different
 exact ((retained_exact ..).mp ((check_exact ..).mp checked other member different)).1.1

theorem checked_external (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (checked : check state owner = true) (freshExternal : External fresh) :
 ExternalState (rebase state owner fresh) := by
 intro other member
 by_cases same : other = owner
 · subst other; simpa only [rebase_at] using freshExternal
 · rw [rebase_other state owner other fresh same]
   obtain ⟨⟨_,external⟩,active⟩ := (retained_exact ..).mp ((check_exact ..).mp checked other member same)
   exact (external_active_exact _ _ external).mpr active

theorem old_check_suffices (state : State Name Owner) (owner : Owner)
 (checked : GeneralPresenceOwnerTableCheck244.check state owner = true) : check state owner = true := by
 apply (check_exact ..).mpr
 intro other member different
 obtain ⟨⟨disjoint,external⟩,cross⟩ := (GeneralPresenceCrossRead244.retainedCheck_exact ..).mp
   ((GeneralPresenceOwnerTableCheck244.check_exact ..).mp checked other member different)
 apply (retained_exact ..).mpr
 refine ⟨⟨disjoint,external⟩,?_⟩
 intro entry _ name _ term found
 exact cross (name,term) (lookup_member found)

def unusedState : State Nat Nat where
 base := []
 owners := [0,1]
 entries := fun owner => if owner = 0 then [(2,.var 3)] else [(3,.var 1)]

theorem unused_new_pass : check unusedState 0 = true := by decide

theorem unused_old_fail : GeneralPresenceOwnerTableCheck244.check unusedState 0 = false := by decide

/-- An unchanged row read does not trigger a typed replacement lookup. -/
def rowOnly : TyTerm Nat := .arrow .bottom (.var 2) .bottom .empty

theorem row_only_pass : activeCheck ([(2,.var 3)] : List (Entry Nat)) [(3,rowOnly)] = true := by decide

theorem row_only_unchanged : rowOnly.subst (substitution [(2,.var 3)]) = rowOnly := rfl
end Yulang.GeneralPresenceUsedTable245
