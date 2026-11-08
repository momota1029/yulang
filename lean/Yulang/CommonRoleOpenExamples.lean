import Yulang.CommonRoleOpenNormalization
import Yulang.CommonRoleOpenState

/-! Local X15/X16 normalization evidence only. These theorems do NOT change
the outer-resolver conformance status: no resolver call is hidden here. -/
namespace Yulang.CommonRoleOpenExamples
open CommonRoleSettledSyntax CommonRoleOpenNormalization

def listConstructor : Constructor := .nominal 0
def boxConstructor : Constructor := .nominal 1

/-- For every A,B, the two known box heads under list are exposed recursively.
No equality of A and B or depth bound is required. -/
theorem x15_local (A B : Ty) :
    normalize (.wrap listConstructor (.wrap boxConstructor A))
      (.wrap listConstructor (.wrap boxConstructor B)) =
      .wrap listConstructor (.wrap boxConstructor (normalize A B)) := by
  simp only [normalize_same]

/-- For every A,B, unlike heads beneath list remain an endpoint pair. -/
theorem x16_local (A B : Ty) :
    normalize (.wrap listConstructor (.wrap boxConstructor A))
      (.wrap listConstructor (.wrap listConstructor B)) =
      .wrap listConstructor (.interval (.wrap boxConstructor A) (.wrap listConstructor B)) := by
  rw [normalize_same, normalize_different]
  decide

/-- The example is genuinely non-singleton in endpoint syntax. This asserts
no Common semantic consistency of these opaque endpoint names. -/
theorem unequal_endpoint_example :
    Ty.wrap boxConstructor (.atom .int) ≠ Ty.wrap boxConstructor (.atom (.named 2)) := by
  intro h
  cases h

end Yulang.CommonRoleOpenExamples
