import Yulang.GeneralDeclarativeCopyK2326

namespace Yulang.GeneralDeclarativeCopiedPending326
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Origin Supported restriction backed_iff)
open GeneralDeclarativeGraphRows321 (observed pending_nominal_self_cycle)
open GeneralDeclarativeK2Alias321 (AliasCycle cycle_in_alias_graph)
open GeneralDeclarativeAuthorizedCopy326 (name writing extended copy fresh)
open GeneralDeclarativeCopyCollapse326 (copy_collapses)
open GeneralDeclarativeLowerKnown321 (Knows)

abbrev pending : Equation := ⟨1,.nominal 0 [.variable 1]⟩
abbrev state : State := ⟨⟨[],[]⟩,[pending]⟩
abbrev notReady : Nat → Prop := fun _ => False

def evidence : Supported state notReady :=
  ⟨fun e o => e = pending ∧ o = .output 42,fun h => by rw [h.1]; exact List.mem_cons_self⟩

theorem no_backed {e : Equation} : e ∉ (restriction evidence).equations := by
  intro included
  obtain ⟨_,⟨_,rfl⟩,available⟩ := (backed_iff evidence e).mp included
  cases available with
  | completed notDone => exact notDone

theorem copied_stays_unbacked : writing state 1 [] ∉ (restriction (copy evidence 1 [])).equations := by
  apply GeneralDeclarativeAuthorizedCopy326.no_new_origin
  · rintro tag ⟨row,present,_,_⟩
    exact no_backed present
  · exact fresh 1 []

theorem ordinary_cycle_copied :
    AliasCycle (extended state 1 []) (observed (extended state 1 [])) (name state 1 []) := by
  apply (GeneralDeclarativeCopyK2326.exact 1 [] _).mpr
  rw [copy_collapses]
  exact cycle_in_alias_graph (pending_nominal_self_cycle evidence 42 ⟨rfl,rfl⟩)

end Yulang.GeneralDeclarativeCopiedPending326
