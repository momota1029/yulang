import Yulang.GeneralDeclarativeWitnessNativeDirectSource361
import Yulang.GeneralDeclarativeWitnessSequentialReceiver361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 59000
set_option maxHeartbeats 57000000
namespace Yulang.GeneralDeclarativeWitnessNativePortTransport361
open GeneralDeclarativeWitnessNativeDirectSource361 (Wire Direct sourceRoute actualWire)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence sequence)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessReleasedForward360 (originalBody forwardKey forwardDemand fixed)
open GeneralDeclarativeWitnessNativePipeline360 (authority valueCode)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority ExactRelease checkExactRelease checked_exact_written_value)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralDeclarativeWitnessNativeValue360 (Value)
open GeneralDeclarativeWitnessNativePreparation360 (context)
open GeneralDeclarativeWitnessCompiler350 (portNames trip trip_injective printDemand)
open GeneralDeclarativeWitnessReleasedObservation360 (observe actualRead)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)

structure Port {negative : Bool} {r : Run negative} (s : Sequence r) (gate : ReleaseAuthority) (w : Wire) where
  stated : Direct r.env forwardKey forwardDemand r.typed.write.address w
  release : ExactRelease s.final.board gate r.typed.write
  atChild : s.continuation.kids[w.clausePosition]? = some s.receiver
  atInput : s.receiver.arguments[w.operandPosition]? = some s.place
  atSeed : ((fixed s.ordinaryChild.final).spans[w.headPosition]?).map
    (fun item => (item.1,trip item.2)) = some (w.binder,trip stated.seed)

/-- The SourceRoute is recomputed from the original declarations and
point demand. The prepared result is used only for verifying the exact
copy on the actual child position, not for guessing a source or grant. -/
def transport {negative} {r : Run negative} (s : Sequence r) (gate : ReleaseAuthority) (w : Wire) :
    Option (Port s gate w) := do
  let a ← sourceRoute r.env forwardKey forwardDemand r.typed.write.address w
  let released ← checkExactRelease s.final.board gate r.typed.write
  if index : w.clausePosition = 0 ∧ w.operandPosition = 0 then
    if anchored : ((fixed s.ordinaryChild.final).spans[w.headPosition]?).map
        (fun item => (item.1,trip item.2)) = some (w.binder,trip a.seed) then
      have child : s.continuation.kids[w.clausePosition]? = some s.receiver := by
        rw [s.exactReceiver,index.1]; rfl
      have arg : s.receiver.arguments[w.operandPosition]? = some s.place := by
        rw [s.args,index.2]; rfl
      some ⟨a,released,child,arg,anchored⟩
    else none
  else none

inductive Part | lower | center | upper deriving DecidableEq

def endpoint (a : Capture) : Part → Nat
  | .lower => a.lower
  | .center => a.center
  | .upper => a.upper

/-- A projected typed read of the corresponding protected point. This
names the origin of the native observation on a specific port; it is
not a write to the raw board at the fresh endpoint numerals. -/
def view {negative r s gate w} (a : @Port negative r s gate w) (v : NativeViews) (which : Part) : Option Value :=
  v (endpoint a.stated.seed which)

theorem port_copies_actual_binder {negative} {r : Run negative} {s : Sequence r} {gate w}
    (a : Port s gate w) :
    s.place = (portNames (context r.env forwardDemand s.continuation.impl
      (fixed s.ordinaryChild.final)) s.continuation.ports).input w.binder := by
  have proof := GeneralDeclarativeWitnessNativeDirectSource361.actual_compiler_position a.stated s.continuation
  rw [a.atChild] at proof
  change s.receiver.arguments[w.operandPosition]? = _ at proof
  rw [a.atInput] at proof
  exact Option.some.inj proof

theorem every_projected_endpoint_is_the_released_value {negative} {r : Run negative}
    {s : Sequence r} {gate w} (a : Port s gate w) (m : Assignment) (v : NativeViews)
    (fit : Fits s.final m v) (which : Part) :
    view a v which = some (r.typed.write.code.eval m) := by
  have seen := checked_exact_written_value (w := s.final) a.release m v fit
  cases which
  · simpa only [view,endpoint,a.stated.seedPoint.1] using seen
  · simpa only [view,endpoint,a.stated.seedPoint.2.1] using seen
  · simpa only [view,endpoint,a.stated.seedPoint.2.2] using seen

def gateFor {negative r} (s : @Sequence negative r) (gate : ReleaseAuthority) (w : Wire) : Bool :=
  (transport s gate w).isSome

theorem actual_route_has_checked_origin (negative : Bool) :
    ((originalBody negative).bind fun r => (sequence r).map fun s => gateFor s authority actualWire).getD false = true := by
  cases negative <;> decide +kernel

def wrongOccurrence : Wire := {actualWire with child := ⟨[7,1],75,3⟩}
def wrongDeclarationOrder : Wire := {actualWire with child := ⟨[7,0],75,1⟩}
def wrongOperand : Wire := {actualWire with operandPosition := 1}
def wrongBinder : Wire := {actualWire with binder := 91}
def wrongClause : Wire := {actualWire with clauseId := 81}

def noSpoof {negative r} (s : @Sequence negative r) : Bool :=
  !gateFor s authority wrongOccurrence &&
  !gateFor s authority wrongDeclarationOrder &&
  !gateFor s authority wrongOperand &&
  !gateFor s authority wrongBinder &&
  !gateFor s authority wrongClause &&
  !gateFor s ⟨[]⟩ actualWire

theorem same_demand_is_not_authority (negative : Bool) :
    ((originalBody negative).bind fun r => (sequence r).map noSpoof).getD false = true := by
  cases negative <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessNativePortTransport361
