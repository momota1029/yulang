import Yulang.GeneralDeclarativeI65I74WrittenPath460

namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
private def key : KeyRead
  | 0 => .emptyRow
  | 100 => .binaryPair
  | 200 => .covariantPoint
  | 201 => .deferredNominal
  | _ => .opaque

private def unsupported : Term := .join (.var 71) (.app 201 (.cons (.var 77) .nil))
private def terminal : Term := .var 8
private def row : Term := .record 10 terminal (.record 10 (.var 9) (.app 0 .nil))
private def root : Term :=
  .record 1 (.variant 7 (.app 100
    (.cons unsupported (.cons (.app 200 (.cons row .nil)) .nil))))
    (.record 2 unsupported (.app 0 .nil))
private def addresses : List Address := [.field 1,.tag 7,.arg 1,.arg 0,.field 10]
example : Walk key root addresses terminal := (read_walk_iff _ _ _ _).mp rfl
example : readWalk key root [.field 1,.tag 8,.arg 1,.arg 0,.field 10] = none := rfl
example : readWalk key root [.field 1,.tag 7,.arg 0,.arg 0] = none := rfl
example : readStep key (.record 10 terminal (.var 7)) (.field 10) = none := rfl
example : readStep key (.app 201 (.cons row .nil)) (.arg 0) = none := rfl
example : readStep key (.app 200 (.cons row (.cons terminal .nil))) (.arg 0) = none := rfl
example : readStep key (.var 7) (.field 10) = none := rfl

#print axioms closed_spine_iff
#print axioms read_field_iff
#print axioms read_step_iff
#print axioms read_walk_iff
end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
