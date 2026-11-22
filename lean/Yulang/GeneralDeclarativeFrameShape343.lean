import Yulang.GeneralDeclarativePlacement343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 6200000
namespace Yulang.GeneralDeclarativeFrameShape343
open GeneralDeclarativeLogicalChild343 (stage capture output built jobs fresh)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativePlacement343 (view rows bridge actual symbolic)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeVersionedRootShape342 (typePoint)
open GeneralDeclarativeInitialModels343 (parts first_capture second_capture)
open GeneralDeclarativeAggregate324 (span ready aligned)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open PresenceNormalForm (Atom)

noncomputable abbrev b0 := capture kept 0
noncomputable abbrev b1 := capture kept 1
noncomputable abbrev e0 : Equation := ⟨symbolic.lower,.variant 0 (.variable b0.lower)⟩
noncomputable abbrev e1 : Equation := ⟨symbolic.center,.variant 0 (.variable 2)⟩
noncomputable abbrev e2 : Equation := ⟨symbolic.upper,.variant 0 (.variable b0.upper)⟩
noncomputable abbrev childRows := [e0,e1,e2]

def edges (b : Capture) : List (Atom Nat) :=
  [.tyLe (.var 2) (.var 2),.tyLe (.var 2) (.var 2),
   .tyLe (.var b.lower) (.var 2),.tyLe (.var 2) (.var b.lower),
   .tyLe (.var b.upper) (.var 2),.tyLe (.var 2) (.var b.upper),
   .tyLe (.var b.lower) (.var 2),.tyLe (.var 2) (.var b.upper)]

theorem retained_constraints :
    view.normal.ordinary = edges b0 ++ edges b1 := rfl

theorem exact_intervals :
    view.normal.intervals = [(symbolic.lower,symbolic.center),(symbolic.center,symbolic.upper)] := rfl

theorem exact_rows :
    view.equations = [publicRow,e0,e1,e2,ownerOutput,
      bridge actual.lower symbolic.lower,bridge actual.center symbolic.center,bridge actual.upper symbolic.upper] := rfl

theorem source_ordinary (row : Equation) (fromSource : GeneralDeclarativeInitialRoot343.InputOrigin row) :
    row ∈ view.equations := by
  rw [GeneralDeclarativeInitialRoot343.origin_unique fromSource,exact_rows]
  exact List.mem_cons_self

theorem output_ordinary (row : Equation) (there : row ∈ childRows) :
    row ∈ view.equations := by
  rw [exact_rows]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ there)

theorem grows : GeneralDeclarativeGrowth327.Extends observedRoot view :=
  ⟨(by intro _ h; cases h),(by intro _ h; cases h),fun row h => by
    cases List.mem_singleton.mp h
    exact source_ordinary _ GeneralDeclarativeInitialRoot343.anchored⟩

end Yulang.GeneralDeclarativeFrameShape343
