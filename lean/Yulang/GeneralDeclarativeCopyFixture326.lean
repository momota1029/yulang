import Yulang.GeneralDeclarativeAuthorizedCopy326
import Yulang.GeneralDeclarativeLateWithProvider326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCopyFixture326
open GeneralDeclarativeAuthorizedCopy326 (copy name writing fresh conservative)
open GeneralDeclarativeCovariantState326 (final assignment models)
open GeneralDeclarativeCovariantSupport326 (controlled child_waits scalarRow)
open GeneralDeclarativeLateProvider326 (completed earlier_complete)
open GeneralDeclarativePairDecl326 (leftArg child)
open GeneralDeclarativeLowerKnown321 (Knows knows_row)
open GeneralDeclarativeOrigins321 (restriction from_completed)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeFootprint321 (stateNames)

abbrev keep : List Nat := [5,6]

theorem absent_before :
    writing final 3 keep ∉ (restriction (copy (controlled (fun _ => False)) 3 keep)).equations := by
  apply GeneralDeclarativeAuthorizedCopy326.no_new_origin _ _ _ ?_ (fresh _ _)
  intro tag discovered
  apply child_waits (fun _ => False) id
  intro actual used
  cases List.mem_singleton.mp used
  exact ⟨tag,discovered⟩

theorem after_real_owner :
    Knows (restriction (copy (controlled completed) 3 keep)) (name final 3 keep) (.primitive (.scalar .int) 0) := by
  apply GeneralDeclarativeAuthorizedCopy326.authorized
  exact knows_row (from_completed (controlled completed)
    (show (controlled completed).derivesFrom scalarRow (.output 42) from .inr (.inl ⟨rfl,rfl⟩)) earlier_complete) rfl

theorem same_models_for_copied_name (swap : Bool) :
    ∃ later, Models (GeneralDeclarativeAuthorizedCopy326.extended final 3 keep) later ∧
      later 5 = assignment swap 5 ∧ later 6 = assignment swap 6 := by
  obtain ⟨later,valid,kept⟩ := conservative 3 keep _ (models swap)
  exact ⟨later,valid,kept 5 (List.mem_append_right _ List.mem_cons_self),
    kept 6 (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

end Yulang.GeneralDeclarativeCopyFixture326
