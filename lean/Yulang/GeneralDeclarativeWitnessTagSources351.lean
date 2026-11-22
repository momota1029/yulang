import Yulang.GeneralDeclarativeWitnessAuthAllocation351
import Yulang.GeneralDeclarativeTaggedNamedPatch340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagSources351
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeWitnessOrigins350 (Table Attached visible support)
open GeneralDeclarativeWitnessReleased350 (link usable)
open GeneralDeclarativeTaggedSources340 (Read BoundsRead merge)
open GeneralDeclarativeTaggedNamed340 (Source)
open GeneralDeclarativeAlternativeView333 (Offer)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessBound349 (Range fits bounds_sound)
open GeneralDeclarativeDemand320 (Bounds)

structure Ref where
  index : Nat
  alias : GeneralDeclarativeWitnessManifest349.Link

def offer {s : State} {t : Table} (a : Attached s t) (root : Nat) (w : Ref) :
    Option (Offer (restriction (support a)) root) := do
  match stored : (visible t)[w.index]? with
  | none => none
  | some e =>
    let own ← link a root e.left w.alias
    pure ⟨e.left,e.right,own.property,usable a stored⟩

structure Inline {s : State} {t : Table} (a : Attached s t) (root tag : Nat) where
  payload : Expr
  read : Read (support a) root tag payload

/-- Direct merge uses the literal recorded RHS, not a rebuilt row. -/
def inline {s : State} {t : Table} (a : Attached s t) (root tag : Nat) (w : Ref) :
    Option (Inline a root tag) := do
  let source ← offer a root w
  match actual : merge tag source.rhs with
  | none => none
  | some payload => pure ⟨payload,⟨source.rhs,⟨source.owner,source.linked,source.stored⟩,actual⟩⟩

inductive Script where
  | tagged
  | join (first last : Script)
  | named (owner : Ref) (remaining : Script)

structure Named {s : State} {t : Table} (a : Attached s t) (tag : Nat) (raw : Expr) where
  payload : Expr
  actual : Source (restriction (support a)) tag raw payload

/-- Branch-local named lookup preserves the recorded row and exact
logical name at every edge. No resulting premise can mistake this
expanded proof for an independently stored literal merged row. -/
def named {s : State} {t : Table} (a : Attached s t) (tag : Nat) :
    (raw : Expr) → Script → Option (Named a tag raw)
  | .variant tag' payload,.tagged =>
    if equals : tag' = tag then some ⟨payload,equals.symm ▸ .tagged⟩ else none
  | .join l r,.join left right => do
    let one ← named a tag l left
    let two ← named a tag r right
    pure ⟨.join one.payload two.payload,.join one.actual two.actual⟩
  | .variable n,.named reference later => do
    let row ← offer a n reference
    let body ← named a tag row.rhs later
    pure ⟨body.payload,.named row body.actual⟩
  | _,_ => none
termination_by _ code => sizeOf code

structure DirectBounds {s : State} {t : Table} (a : Attached s t) (arg : Capture) (tag : Nat) where
  lower : Expr
  upper : Expr
  fact : BoundsRead (support a) arg tag lower upper

def directBounds {s : State} {t : Table} (a : Attached s t) (arg : Capture) (tag : Nat)
    (span : Range) (l h : Ref) : Option (DirectBounds a arg tag) := do
  if good : fits s arg span = true then
    let lo ← inline a arg.lower tag l
    let hi ← inline a arg.upper tag h
    pure ⟨lo.payload,hi.payload,⟨bounds_sound good,lo.read,hi.read⟩⟩
  else none

structure NamedBounds {s : State} {t : Table} (a : Attached s t) (arg : Capture) (tag : Nat) where
  lower : Named a tag (.variable arg.lower)
  upper : Named a tag (.variable arg.upper)
  fact : Bounds s arg

def namedBounds {s : State} {t : Table} (a : Attached s t) (arg : Capture) (tag : Nat)
    (span : Range) (l h : Script) : Option (NamedBounds a arg tag) := do
  if good : fits s arg span = true then
    let lo ← named a tag (.variable arg.lower) l
    let hi ← named a tag (.variable arg.upper) h
    pure ⟨lo,hi,bounds_sound good⟩
  else none

end Yulang.GeneralDeclarativeWitnessTagSources351
