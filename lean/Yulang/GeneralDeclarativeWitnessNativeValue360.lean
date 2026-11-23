import Yulang.GeneralDeclarativeWitnessNativePreparation360
import Yulang.GeneralDeclarativeWitnessTypedRelease354

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNativeValue360
open GeneralDeclarativeWitnessNominalSource359 (Route SlotRead)
open GeneralDeclarativeWitnessScopedBindings359 (slots read_has_literal_frame)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Wire Described describe)
open GeneralDeclarativeWitnessTypedRelease354 (Stamp)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty)
open CommonDeclaredNominalInspection (Registry)

/-- A finite native observation. The constructor is never encoded as an
ordinary invariant type; only a leaf reads an ordinary captured value. -/
inductive Code where
  | leaf (slot : Nat)
  | nullary (key : Nat)
  | unary (key : Nat) (argument : Code)
  deriving DecidableEq, Repr

inductive Value where
  | leaf (payload : Ty)
  | nullary (key : Nat)
  | unary (key : Nat) (argument : Value)

def Code.eval (m : Assignment) : Code → Value
  | .leaf n => .leaf (m n).1
  | .nullary n => .nullary n
  | .unary key child => .unary key (child.eval m)

def emit (locals : SlotRead) : Route → Option Code
  | .bind n => (locals n).map fun c => .leaf c.center
  | .nullary n => some (.nullary n)
  | .unary n rest => (emit locals rest).map (.unary n)

inductive FromCenters (locals : SlotRead) : Route → Code → Prop where
  | leaf : locals binder = some c → FromCenters locals (.bind binder) (.leaf c.center)
  | nil : FromCenters locals (.nullary n) (.nullary n)
  | cons : FromCenters locals inner code → FromCenters locals (.unary n inner) (.unary n code)

theorem emitted_exact {locals route code} : emit locals route = some code ↔ FromCenters locals route code := by
  constructor
  · intro generated
    induction route generalizing code with
    | bind n =>
      cases actual : locals n with
      | none => simp [emit,actual] at generated
      | some c =>
        have same : Code.leaf c.center = code := by simpa [emit,actual] using generated
        subst code
        exact .leaf actual
    | nullary n =>
      have same : Code.nullary n = code := by simpa [emit] using generated
      subst code
      exact .nil
    | unary n rest ih =>
      cases actual : emit locals rest with
      | none => simp [emit,actual] at generated
      | some inner =>
        have same : Code.unary n inner = code := by simpa [emit,actual] using generated
        subst code
        exact .cons (ih actual)
  · intro declared
    induction declared with
    | leaf selected => simp [emit,selected]
    | nil => rfl
    | cons _ ih => simp [emit,ih]

structure Address where
  owner : Stamp
  declarationOrdinal : Nat
  outputOrdinal : Nat
  name : Nat
  target : Nat
  sourceEquation : Nat
  deriving DecidableEq

structure Write where
  address : Address
  code : Code
  deriving DecidableEq

def owner {e frame d l} (_ : Prepared e frame d l) (version : Nat) : Stamp :=
  ⟨frame.occurrence,d.role,frame.declaration,version⟩

def associates {e frame d l} (p : Prepared e frame d l) (table : Registry) (wire : Wire) :=
  describe e table [p.captures] frame d wire

structure Compiled {e frame d l} (p : Prepared e frame d l) (table : Registry) (wire : Wire) (version : Nat) where
  supplied : Described e table [p.captures] frame d wire
  sourceSame : supplied.declaration = p.impl
  code : Code
  produced : emit (slots [p.captures] frame) wire.route = some code

def Compiled.write {e frame d l p table wire version} (a : @Compiled e frame d l p table wire version) : Write :=
  ⟨⟨owner p version,frame.sourceOrdinal,wire.ordinal,a.supplied.requested.name,wire.target,wire.sourceEquation⟩,a.code⟩

def compile {e frame d l} (p : Prepared e frame d l) (table : Registry) (wire : Wire) (version : Nat) :
    Option (Compiled p table wire version) := do
  let a ← associates p table wire
  match source : emit (slots [p.captures] frame) wire.route with
  | none => none
  | some code => some ⟨a,Option.some.inj (a.selectedSource.symm.trans p.authored),code,source⟩

theorem fixed_compiler_capture {e frame d l p table wire version}
    (a : @Compiled e frame d l p table wire version) :
    a.supplied.declaration = p.impl ∧ a.write.address.target = a.supplied.requested.target ∧
      a.write.address.owner = owner p version ∧
      FromCenters (slots [p.captures] frame) wire.route a.write.code :=
  ⟨a.sourceSame,a.supplied.fixed.symm,rfl,emitted_exact.mp a.produced⟩

end Yulang.GeneralDeclarativeWitnessNativeValue360
