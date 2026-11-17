import Yulang.GeneralPresenceOwnerTable244
namespace Yulang.GeneralPresenceOwnerTableCheck244
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244
open GeneralPresenceOwnerTable244
variable {Name Owner : Type} [DecidableEq Name] [DecidableEq Owner]

/-- Checks every retained owner against the actual old block in the table.
Fresh block validity and the removed block's projection conditions are separate. -/
def check (state : State Name Owner) (owner : Owner) : Bool :=
 state.owners.all fun other => if other = owner then true else retainedCheck (state.entries owner) (state.entries other)

theorem check_exact (state : State Name Owner) (owner : Owner) :
 check state owner = true ↔
 ∀ other ∈ state.owners, other ≠ owner → retainedCheck (state.entries owner) (state.entries other) = true := by
 unfold check
 constructor
 · intro valid other member different
   have held := List.all_eq_true.mp valid other member
   simpa [different] using held
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
 exact ((retainedCheck_exact ..).mp ((check_exact ..).mp checked other member different)).1.1

theorem checked_external (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (checked : check state owner = true) (freshExternal : External fresh) :
 ExternalState (rebase state owner fresh) := by
 intro other member
 by_cases same : other = owner
 · subst other; simpa only [rebase_at] using freshExternal
 · rw [rebase_other state owner other fresh same]
   exact GeneralPresenceCrossRead244.checked_external _ _ ((check_exact ..).mp checked other member same)

def exampleState : State Nat Nat where
 base := [.tyLe (.var 4) (.var 2)]
 owners := [0,1]
 entries := fun owner => if owner = 0 then [(2,.var 1)] else [(3,.var 2)]

theorem example_check : check exampleState 0 = true := by decide

theorem example_other : (rebase exampleState 0 [(2,.var 0)]).entries 1 = [(3,.var 1)] := by rfl

theorem example_base : (rebase exampleState 0 [(2,.var 0)]).base = [.tyLe (.var 4) (.var 1)] := by rfl
end Yulang.GeneralPresenceOwnerTableCheck244
