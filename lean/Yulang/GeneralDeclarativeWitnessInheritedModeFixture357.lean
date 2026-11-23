import Yulang.GeneralDeclarativeWitnessSparseIntervals357
import Yulang.GeneralDeclarativeWitnessCoverageFixture357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 43000
set_option maxHeartbeats 38000000
namespace Yulang.GeneralDeclarativeWitnessInheritedModeFixture357
open GeneralDeclarativeWitnessCoverageFixture357 (prepare)
open GeneralDeclarativeWitnessSparseIntervals357 (compile)
open CommonRecursiveNominalIntervals (Endpoint Bounds compileInContext)
open CommonDeclaredNominalInspection (Registry)
open PresenceNormalForm (Atom)

def table : Registry := (List.range 91).map fun key =>
  if key = 20 then [⟨.value,.covariant⟩] else
  if key = 42 then [⟨.value,.contravariant⟩] else
  if key = 55 then [⟨.value,.invariant⟩] else []

def body (name a b : Nat) : Endpoint Nat :=
  .nominal name [.inl (.interval (.ordinary (.var a)) (.ordinary (.var b)))]

def wrapped (name a b : Nat) : Endpoint Nat :=
  .nominal 55 [.inl (.point (body name a b))]

def read (context : Bool) (first last : Endpoint Nat) (registry : Registry := table) : Option (List (Atom Nat)) :=
  prepare.bind fun e => (compile e registry context first last).map (fun x => x.rows)

def order : List (Atom Nat) :=
  [.tyLe (.var 7) (.var 8),.tyLe (.var 7) (.var 10),
   .tyLe (.var 9) (.var 8),.tyLe (.var 9) (.var 10)]

theorem inherited_covariance_is_interval :
    read true (body 20 7 8) (body 20 9 10) = some order := by decide +kernel

theorem inherited_contravariance_is_interval :
    read true (body 42 7 8) (body 42 9 10) = some order := by decide +kernel

theorem covariance_outside_does_not_take_open_argument :
    read false (body 20 7 8) (body 20 9 10) = none := by decide +kernel

theorem nested_invariant_carries_covariance_context :
    ((read false (wrapped 20 7 8) (wrapped 20 9 10)).map List.length) = some 16 := by decide +kernel

theorem nested_invariant_carries_contravariance_context :
    ((read false (wrapped 42 7 8) (wrapped 42 9 10)).map List.length) = some 16 := by decide +kernel

theorem cannot_forge_nested_variance :
    read false (wrapped 20 7 8) (wrapped 20 9 10)
      (table.set 20 [⟨.value,.invariant⟩]) = none := by decide +kernel

theorem dense_filler_alone_would_pass :
    compileInContext table false (.nominal 21 [] : Endpoint Nat) (.nominal 21 []) = some [] := by decide +kernel

theorem sparse_guard_requires_real_named_constructor :
    read false (.nominal 21 []) (.nominal 21 []) = none ∧
    read false (.nominal 90 []) (.nominal 90 []) = some [] := by decide +kernel

end Yulang.GeneralDeclarativeWitnessInheritedModeFixture357
