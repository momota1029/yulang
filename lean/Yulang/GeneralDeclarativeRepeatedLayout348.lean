import Yulang.GeneralDeclarativeRepeatedPlacement348

set_option maxRecDepth 35000
set_option maxHeartbeats 46000000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRepeatedLayout348
open GeneralDeclarativeRepeatedPlacement348 (keep placedView links)
open GeneralDeclarativeReplayStage348 (capture phase tied exact_capture exact_phase)
open GeneralDeclarativeReplayCompile348 (output logicalArg)
open GeneralDeclarativeAggregate324 (ready span)
open GeneralDeclarativeVersionedRootShape342 (typePoint)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open PresenceNormalForm (Atom)

noncomputable abbrev first := capture keep 0
noncomputable abbrev second := span (ready tied keep typePoint [typePoint]) keep typePoint [typePoint]
noncomputable abbrev logical := logicalArg keep

def duplicateEdges (c : Capture) : List (Atom Nat) :=
  [.tyLe (.var 2) (.var 2),.tyLe (.var 2) (.var 2),
   .tyLe (.var 2) (.var 2),.tyLe (.var 2) (.var 2),
   .tyLe (.var c.lower) (.union (.var 2) (.var 2)),.tyLe (.union (.var 2) (.var 2)) (.var c.lower),
   .tyLe (.var c.upper) (.inter (.var 2) (.var 2)),.tyLe (.inter (.var 2) (.var 2)) (.var c.upper),
   .tyLe (.var c.lower) (.var 2),.tyLe (.var 2) (.var c.upper)]

noncomputable abbrev e0 : Equation := ⟨logical.lower,.variant 0 (.variable first.lower)⟩
noncomputable abbrev e1 : Equation := ⟨logical.center,.variant 0 (.variable 2)⟩
noncomputable abbrev e2 : Equation := ⟨logical.upper,.variant 0 (.variable first.upper)⟩
noncomputable abbrev rows := [e0,e1,e2]

theorem ordinary : placedView.normal.ordinary = duplicateEdges first ++ duplicateEdges second := rfl

theorem intervals :
    placedView.normal.intervals = [(logical.lower,logical.center),(logical.center,logical.upper)] := rfl

theorem written : placedView.equations = [publicRow,e0,e1,e2,ownerOutput] ++ links := rfl

theorem exact_compiled : (output keep).equations = [publicRow,e0,e1,e2,ownerOutput] := rfl

end Yulang.GeneralDeclarativeRepeatedLayout348
