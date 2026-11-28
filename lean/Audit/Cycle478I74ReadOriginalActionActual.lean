import Yulang.GeneralDeclarativeI65I74ReadOriginalActionPath478

namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475.OriginalPathActual478
open GeneralDeclarationPatterns (Pattern)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose atSource)

def nested : Pattern := .record 30 (.variant 5 (.app 8 [.var 0,.var 1])) (.app 9 [])
def twice : Pattern := .join nested nested
def repeatedField : Pattern := .record 30 (.var 1) (.record 30 (.var 2) (.app 9 []))
def differentJoin : Pattern := .join nested (.record 31 (.var 1) (.app 9 []))

def observedActions (p : Pattern) (w : List Pose) : Option (List Address × List (List Pose) × Pattern) :=
  (parseOriginalActionPath478 p w).map (fun r => (r.actions,r.segments,r.last))

def coordinatesChecked478 : List Bool :=
  [decide (observedActions twice [.right,.payload,.variant,.app 1] =
      some ([.field 30,.tag 5,.arg 1],[[.right,.payload],[.variant],[.app 1]],.var 1)),
   decide (atSource repeatedField [.tail,.payload] = some (.var 2)),
   (observedActions repeatedField [.tail,.payload]).isNone,
   (observedActions differentJoin [.left,.payload]).isNone,
   (observedActions nested [.payload,.variant,.app 2]).isNone]

theorem the_pose_infers_literal_field_variant_and_argument_but_not_hidden_or_residual_cases478 :
    coordinatesChecked478 = [true,true,true,true,true] := by decide +kernel

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval coordinatesChecked478

#print axioms the_pose_infers_literal_field_variant_and_argument_but_not_hidden_or_residual_cases478
end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475.OriginalPathActual478
