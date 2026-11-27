import Yulang.GeneralDeclarativeI65I74OriginalPhysicalPositions463

namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin
open Yulang.GeneralDeclarationPatterns (Pattern)

#print axioms literal_occurrence
#print axioms exact_original_occurrences
#print axioms selected_occurrence_iff
#print axioms every_existing_normalized_field_step_has_finite_original_position
#print axioms actual_normalized_argument_has_literal_origin
#print axioms route_occurrences_exact
#print axioms whole_route_is_literal_and_preserves_exact_coordinates

private def keys : KeyRead := fun k => if k = 0 then .emptyRow else .opaque
private def empty : Pattern := .app 0 []
private def first : Pattern := .variant 8 (.var 3)
private def stale : Pattern := .variant 8 (.var 9)
private def base : Pattern := .record 7 first (.record 6 (.var 1) (.record 7 stale empty))
private def shorter : Pattern := .record 7 first (.record 6 (.var 1) empty)

-- Published read order is the original left/right order, not display selection.
#guard (locateRoute (fun _ => keys) (.join base shorter) 20 [(.field 7, 33)]).map Prod.fst ==
  [[Pose.left,Pose.payload],[Pose.right,Pose.payload]]

-- To get the second label we skip the physical prior field, not a graph hop.
#guard (locateRoute (fun _ => keys) base 20 [(.field 6, 47)]).map Prod.fst ==
  [[Pose.tail,Pose.payload]]

-- A closed record fixture really preserves both written physical and raw positions.
#guard (locateRoute (fun _ => keys) base 20 [(.field 7, 33),(.variant 8,41)]).map Prod.fst ==
  [[Pose.payload,Pose.variant]]

-- Distinct merged tag payloads do not license picking either source.
#guard (selectedOrigins keys (.join (.variant 8 first) (.variant 8 stale)) (.tag 8)).isEmpty
end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin
