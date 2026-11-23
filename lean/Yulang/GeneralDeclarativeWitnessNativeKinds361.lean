import Yulang.GeneralDeclarativeWitnessNativePortTransport361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 59000
set_option maxHeartbeats 57000000
namespace Yulang.GeneralDeclarativeWitnessNativeKinds361
open GeneralDeclarativeWitnessConstructorModes357 (Environment Mode Use readUse SourceMode)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessReleasedForward360 (originalBody)
open CommonDeclaredNominalVariance (Variance)

inductive KindTag where
  | invariant
  | declaredNullary
  | declaredValue (variance : Variance)
  deriving DecidableEq, Repr

/-- Native unary values are value arguments. A declared row position is
not approximated by a value, and an absent constructor is not nullary. -/
def tag (arity : Nat) (m : Mode) : Option KindTag :=
  match arity,m with
  | 0,.invariant | 1,.invariant => some .invariant
  | 0,.declared [] => some .declaredNullary
  | 1,.declared [⟨.value,v⟩] => some (.declaredValue v)
  | _,_ => none

structure Ctor (e : Environment) (key arity : Nat) where
  use : Use e key arity
  mode : KindTag
  exact : tag arity use.mode = some mode

def readCtor (e : Environment) (key arity : Nat) : Option (Ctor e key arity) := do
  let u ← readUse e key arity
  match h : tag arity u.mode with
  | none => none
  | some found => some ⟨u,found,h⟩

inductive Shaped (e : Environment) : Code → Type where
  | external (name : Nat) : Shaped e (.leaf name)
  | empty (u : Ctor e key 0) : Shaped e (.nullary key)
  | nesting (u : Ctor e key 1) (rest : Shaped e inside) : Shaped e (.unary key inside)

def read (e : Environment) : (c : Code) → Option (Shaped e c)
  | .leaf name => some (.external name)
  | .nullary key => (readCtor e key 0).map .empty
  | .unary key inner => do
    let outer ← readCtor e key 1
    let rest ← read e inner
    pure (.nesting outer rest)

def Shaped.path {e : Environment} : {c : Code} → Shaped e c → List (Nat × KindTag)
  | _,.external _ => []
  | .nullary k,.empty u => [(k,u.mode)]
  | .unary k _,.nesting u rest => (k,u.mode)::rest.path

theorem Ctor.independent_lookup {e : Environment} {key arity} (c : Ctor e key arity) :
    SourceMode e key c.use.mode ∧
    (GeneralSourceMetadataBundle291.registry e.source).constructors key = some c.use.declared ∧
    c.use.declared.parameters.length = arity := by
  have a := GeneralDeclarativeWitnessConstructorModes357.check_has_no_fallback c.use
  exact ⟨c.use.sourced,a.1,a.2.1⟩

def codeMode {negative} (r : Run negative) : Bool :=
  (read r.env r.typed.write.code).map Shaped.path ==
    some [(55,.invariant),(if negative then 42 else 20,.declaredValue (if negative then .contravariant else .covariant))]

theorem actual_nested_declarations_keep_both_modes (negative : Bool) :
    ((originalBody negative).map codeMode).getD false = true := by
  cases negative <;> decide +kernel

def noDefaults {negative} (r : Run negative) : Bool :=
  (read r.env (.nullary 55)).isNone &&
  (read r.env (.unary 999 (.leaf 61))).isNone &&
  (read r.env (.nullary 999)).isNone

theorem no_default_kind_or_arity (negative : Bool) :
    ((originalBody negative).map noDefaults).getD false = true := by
  cases negative <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessNativeKinds361
