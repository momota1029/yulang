import Yulang.GeneralSourceRoleCstJsonOrigin293
import Yulang.GeneralSourceRoleCstWireFixture293

/-! Bound and schema controls for the actual JSON-value reader. -/
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralSourceRoleCstJsonFixture293
open Lean (Json)
open GeneralSourceRoleCstJson293 (read read_exact encode depth)
open GeneralSourceRoleCstJsonEntry293 (extractValue)
open GeneralSourceRoleCstWireFixture293 (raw path expected)

theorem exact_fixture_depth : depth raw = 7 := rfl

theorem wire_at_depth : read 7 (encode raw) = some raw :=
  (read_exact ..).mpr ⟨rfl,by simp [exact_fixture_depth]⟩

theorem shallow_input_declined : read 6 (encode raw) = none := rfl

theorem exact_external_boundary :
    extractValue 7 (encode raw) () 42 path = .ok expected := rfl

theorem outer_shape_errors_distinct :
    extractValue 7 (Json.arr #[.str "node",.str "Root",.arr #[],Json.null]) () 42 path =
      .error .schemaOrDepth ∧
    extractValue 7 (Json.arr #[.str "node",.str "UnknownKind",.arr #[]]) () 42 path =
      .error .unknownTag :=
  ⟨rfl,rfl⟩

end Yulang.GeneralSourceRoleCstJsonFixture293
