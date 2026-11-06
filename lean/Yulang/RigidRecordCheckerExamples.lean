import Yulang.RigidRecordChecker

/-!
# Kernel execution of rigid-tail record comparison

These examples distinguish the rigid-demand contract from the full reference
relation. The opaque-target negatives are a limitation of that relation,
not source-language type-error expectations.
-/

namespace Yulang.RigidRecordCheckerExamples

open StructuralBase (Ty)
open RigidRecordChecker (check checkDemand)

def pureRows (_ _ : Unit) : Bool := true

abbrev integer : Ty Unit := .base .int
abbrev string : Ty Unit := .base .str
abbrev boolean : Ty Unit := .base .bool
abbrev singleton : Ty Unit := .record 0 integer .emptyRecord
abbrev neverTail : Ty Unit := .record 0 integer .bottom
abbrev shadowed : Ty Unit := .record 0 integer (.record 0 string .bottom)
abbrev redundant : Ty Unit := .record 0 integer (.union .emptyRecord .bottom)
abbrev demanded : Ty Unit := .record 0 integer (.record 1 boolean .emptyRecord)
abbrev supplying : Ty Unit := .record 0 integer
  (.union (.record 0 string (.record 1 boolean .emptyRecord))
    (.record 0 boolean (.record 1 boolean .emptyRecord)))
abbrev missingAlternative : Ty Unit := .record 0 integer
  (.union (.record 1 boolean .emptyRecord) (.record 2 boolean .emptyRecord))
abbrev opaqueLeft : Ty Unit := .record 0 boolean (.record 0 integer .bottom)
abbrev opaqueRight : Ty Unit := .record 0 boolean (.record 0 string .bottom)

theorem never_tail_width : check pureRows neverTail .emptyRecord = true := by decide +kernel
theorem never_tail_head : check pureRows neverTail singleton = true := by decide +kernel
theorem never_tail_visible_mismatch :
    check pureRows neverTail (.record 0 string .emptyRecord) = false := by decide +kernel
theorem hidden_never_payload : check pureRows shadowed singleton = true := by decide +kernel
theorem proper_hidden_payload :
    check pureRows (.record 0 integer (.record 0 string .emptyRecord)) singleton = true := by decide +kernel
theorem redundant_forward : check pureRows singleton redundant = true := by decide +kernel
theorem redundant_backward : check pureRows redundant singleton = true := by decide +kernel
theorem union_supply_visible_fields : check pureRows supplying demanded = true := by decide +kernel
theorem union_supply_missing_field : check pureRows missingAlternative demanded = false := by decide +kernel
theorem nonrecord_tail_rejected :
    check pureRows (.record 0 integer string) .emptyRecord = false := by decide +kernel

/-- Both types have admissible tails, but the target is not a rigid view.
The exact reference checker still distinguishes their hidden payloads. -/
theorem opaque_hidden_forward : check pureRows opaqueLeft opaqueRight = false := by decide +kernel
theorem opaque_hidden_backward : check pureRows opaqueRight opaqueLeft = false := by decide +kernel

theorem rigid_demand_hidden_payload :
    checkDemand pureRows shadowed singleton (.field .empty) = true := by decide +kernel
theorem rigid_demand_hidden_target :
    checkDemand pureRows neverTail (.record 0 integer (.record 0 string .emptyRecord))
      (.field (.field .empty)) = true := by decide +kernel
theorem rigid_demand_visible_mismatch :
    checkDemand pureRows shadowed (.record 0 string .emptyRecord) (.field .empty) = false := by decide +kernel
theorem rigid_demand_union :
    checkDemand pureRows supplying demanded (.field (.field .empty)) = true := by decide +kernel
theorem rigid_demand_bad_tail :
    checkDemand pureRows (.record 0 integer string) singleton (.field .empty) = false := by decide +kernel

def boolRows (left right : Bool) : Bool := !left || right

theorem input_row_contravariant :
    check boolRows (.arrow (.base .int) true (.base .int) false)
      (.arrow (.base .int) false (.base .int) false) = true := by decide +kernel
theorem input_row_reverse_rejected :
    check boolRows (.arrow (.base .int) false (.base .int) false)
      (.arrow (.base .int) true (.base .int) false) = false := by decide +kernel

def cases : List (String × Ty Unit × Ty Unit × Bool) :=
  [ ("never tail has record width", neverTail, .emptyRecord, true)
  , ("never tail exposes the head", neverTail, singleton, true)
  , ("visible payload mismatch", neverTail, .record 0 string .emptyRecord, false)
  , ("hidden payload above never", shadowed, singleton, true)
  , ("hidden payload in a proper supply", .record 0 integer (.record 0 string .emptyRecord), singleton, true)
  , ("redundant tail forward", singleton, redundant, true)
  , ("redundant tail backward", redundant, singleton, true)
  , ("union supply with visible common fields", supplying, demanded, true)
  , ("union supply missing a demanded field", missingAlternative, demanded, false)
  , ("nonrecord tail", .record 0 integer string, .emptyRecord, false)
  , ("opaque reference boundary forward", opaqueLeft, opaqueRight, false)
  , ("opaque reference boundary backward", opaqueRight, opaqueLeft, false)
  ]

def demandCases : List (String × Bool × Bool) :=
  [ ("rigid demand ignores hidden supplied payload", checkDemand pureRows shadowed singleton (.field .empty), true)
  , ("rigid demand ignores hidden demanded payload", checkDemand pureRows neverTail
      (.record 0 integer (.record 0 string .emptyRecord)) (.field (.field .empty)), true)
  , ("rigid demand rejects visible mismatch", checkDemand pureRows shadowed
      (.record 0 string .emptyRecord) (.field .empty), false)
  , ("rigid demand checks both union supplies", checkDemand pureRows supplying demanded (.field (.field .empty)), true)
  , ("rigid demand rejects nonrecord tail", checkDemand pureRows (.record 0 integer string) singleton (.field .empty), false)
  ]

end Yulang.RigidRecordCheckerExamples
