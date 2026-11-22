import Yulang.GeneralDeclarativeWitnessManifest349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecord349
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeWitnessManifest349 (Manifest Attached support Code)
open GeneralDeclarativeWitnessBound349 (Range fits bounds_sound)
open GeneralDeclarativeEndpointRecord336 (Read interp)
open GeneralDeclarativeExactDelete337 (subtract)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordResidual323 (withTail)
open CommonRoleCanonicalRows (Row normalize residual)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)

structure Wire where
  bounds : Range
  lower : Code
  upper : Code

structure Checked {s : State} {m : Manifest} (a : Attached s m)
    (arg : Capture) (keys : List Nat) where
  lower : Row Expr
  upper : Row Expr
  displayedLower : Row Expr
  displayedUpper : Row Expr
  lowerEnd : Expr
  upperEnd : Expr
  fact : Read (support a) arg keys lower upper displayedLower displayedUpper lowerEnd upperEnd

/-- Finite I-61 endpoint reader. Bounds are checked against the actual
center identity; no center row, supported or otherwise, is required.
Order and deletion use the existing normal form, not the witness's
claimed order or a mask. -/
def decode {s : State} {m : Manifest} (a : Attached s m) (arg : Capture) (keys : List Nat) (w : Wire) :
    Option (Checked a arg keys) :=
  if h : fits s arg w.bounds = true then
    if unique : keys.Nodup then do
      let lo ← GeneralDeclarativeWitnessManifest349.replay a arg.lower w.lower
      let hi ← GeneralDeclarativeWitnessManifest349.replay a arg.upper w.upper
      match l : order (normalize lo.fields) keys, u : order (normalize hi.fields) keys with
      | some first,some last =>
        pure ⟨lo.fields,hi.fields,first,last,lo.ending,hi.ending,
          ⟨bounds_sound h,unique,lo.spine,hi.spine,l,u⟩⟩
      | _,_ => none
    else none
  else none

def check {s : State} {m : Manifest} (a : Attached s m) (arg : Capture) (keys : List Nat) (wire : Wire) : Bool :=
  (decode a arg keys wire).isSome

theorem present {s : State} {m : Manifest} {a : Attached s m} {arg : Capture}
    {keys : List Nat} {wire : Wire} (h : check a arg keys wire = true) :
    Nonempty (Checked a arg keys) := by
  unfold check at h
  cases run : decode a arg keys wire with
  | none => simp [run] at h
  | some out => exact ⟨out⟩

theorem exact_labels {s : State} {m : Manifest} {a : Attached s m} {arg : Capture}
    {keys : List Nat} (r : Checked a arg keys) :
    r.displayedLower.map Prod.fst = keys ∧ r.displayedUpper.map Prod.fst = keys :=
  GeneralDeclarativeEndpointRecord336.labels r.fact

theorem residual_same_model {s : State} {m : Manifest} {a : Attached s m}
    {arg : Capture} {keys : List Nat} (r : Checked a arg keys) (model : Assignment) (fit : Models s model) :
    InInterval (interp model (withTail (residual keys (normalize r.lower)) r.lowerEnd))
      (interp model (withTail (residual keys (normalize r.upper)) r.upperEnd))
      (subtract keys (model arg.center).1) :=
  GeneralDeclarativeExactDeleteAuth337.supported r.fact model fit

theorem field_same_model {s : State} {m : Manifest} {a : Attached s m}
    {arg : Capture} {keys : List Nat} (r : Checked a arg keys)
    {key : Nat} {e q : Expr} (lo : (key,e) ∈ r.displayedLower) (hi : (key,q) ∈ r.displayedUpper)
    (model : Assignment) (fit : Models s model) :
    ∃ center, GeneralDeclarativeRecordChannel330.project key false [] (model arg.center).1 = some center ∧
      InInterval (interp model e) (interp model q) center :=
  GeneralDeclarativeEndpointRecord336.field_interval r.fact lo hi model fit

end Yulang.GeneralDeclarativeWitnessRecord349
