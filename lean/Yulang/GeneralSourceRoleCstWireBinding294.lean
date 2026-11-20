import Yulang.GeneralSourceRoleCstStrictTransport294

/-! Compare retained wire directly instead of trusting a repeated brand or
compact tree equality. This does not identify the producer environment. -/
namespace Yulang.GeneralSourceRoleCstWireBinding294
open GeneralSourceRoleCstWire293 (Wire)

mutual
def same : Wire → Wire → Bool
  | .token a x,.token b y => a == b && x == y
  | .node a cs,.node b ds => a == b && sameList cs ds
  | _,_ => false
def sameList : List Wire → List Wire → Bool
  | [],[] => true
  | c::cs,d::ds => same c d && sameList cs ds
  | _,_ => false
end

mutual
theorem same_exact (a b : Wire) : same a b = true ↔ a = b := by
  cases a with
  | token k s => cases b <;> simp [same]
  | node k cs =>
    cases b with
    | token q t => simp [same]
    | node q ds => simp [same,same_list_exact cs ds]
theorem same_list_exact (cs ds : List Wire) : sameList cs ds = true ↔ cs = ds := by
  cases cs with
  | nil => cases ds <;> simp [sameList]
  | cons c cs =>
    cases ds with
    | nil => simp [sameList]
    | cons d ds => simp [sameList,same_exact c d,same_list_exact cs ds]
end

open GeneralSourceRoleCstVisibleReceipt294 (project)
open GeneralSourceRoleCstMixedReceipt294 (Receipt)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleTrack292 (Tracked)

structure BoundReceipt (Brand : Type) where
  fromWire : Wire
  diagnostics : Receipt Brand

def useBound {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (retained : Wire) (brand : Brand) (a : Address Brand) (external : BoundReceipt Brand) :
    Option (Tracked Scope (Address Brand)) :=
  if same external.fromWire retained then project policy scope retained brand a external.diagnostics
  else none

theorem use_bound_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (retained : Wire) (brand : Brand) (a : Address Brand)
    (external : BoundReceipt Brand) (out : Tracked Scope (Address Brand)) :
    useBound policy scope retained brand a external = some out ↔
    external.fromWire = retained ∧ project policy scope retained brand a external.diagnostics = some out := by
  by_cases h : same external.fromWire retained = true
  · simp [useBound,same_exact,(same_exact ..).mp h]
  · have nope : external.fromWire ≠ retained := fun e => h ((same_exact ..).mpr e)
    simp [useBound,h,nope]

theorem compact_equality_cannot_bind_wire :
    GeneralSourceRoleCstWire293.decode (.token "Unknown" "@") =
      GeneralSourceRoleCstWire293.decode (.token "Error" "@") ∧
    same (.token "Unknown" "@") (.token "Error" "@") = false := ⟨rfl,rfl⟩

end Yulang.GeneralSourceRoleCstWireBinding294
