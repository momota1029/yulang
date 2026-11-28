import Yulang.GeneralDeclarativeI65I74TypedVisibleRead482

namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank.VisibleActual
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table)

def selected : Equation := ⟨7,.primitive .emptyRecord []⟩
def pendingAlias : Equation := ⟨6,.variable 7⟩
def catalogue : Table := ⟨[selected],[(pendingAlias,99),(selected,10),(selected,11)],[10]⟩

theorem two_equal_rows_keep_different_real_issuance_indices :
    (visibleWithAuthority catalogue)[0]? = some (.authored 0,selected) ∧
    (visibleWithAuthority catalogue)[1]? = some (.completed 1 10,selected) ∧
    (visibleWithAuthority catalogue)[2]? = none ∧
    ReadRowAuthority.Valid catalogue selected (.completed 1 10) ∧
    ¬ReadRowAuthority.Valid catalogue selected (.completed 1 11) := by
  refine ⟨rfl,rfl,rfl,⟨rfl,List.mem_cons_self ..⟩,?_⟩
  intro h
  exact (by decide : 11 ∉ catalogue.released) h.2

/-- info: [true, true, false, true] -/
#guard_msgs in
#eval [
  ((visibleWithAuthority catalogue)[0]?).isSome,
  ((visibleWithAuthority catalogue)[1]?).isSome,
  ((visibleWithAuthority catalogue)[2]?).isSome,
  ((visibleWithAuthority {catalogue with released := [99]})[1]?).map
    (fun p => p.1 == ReadRowAuthority.completed 0 99) == some true]

#print axioms two_equal_rows_keep_different_real_issuance_indices
end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank.VisibleActual
