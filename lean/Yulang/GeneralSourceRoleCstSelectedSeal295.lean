import Yulang.GeneralSourceRoleCstBindingControl294

/-! A declaration-specific, explicitly supplied gate. A diagnostic receipt is
reusable across selections; this wrapper additionally fixes the requested
address and policy. It authenticates neither approvals nor producer identity. -/
namespace Yulang.GeneralSourceRoleCstSelectedSeal295
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstWireBinding294 (BoundReceipt useBound use_bound_exact)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleTrack292 (Tracked)

structure Selection (Brand : Type) where
  address : Address Brand
  policy : Policy
  receipt : BoundReceipt Brand

def select {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (retained : Wire) (brand : Brand) (asked : Address Brand) (packet : Selection Brand) :
    Option (Tracked Scope (Address Brand)) :=
  if asked = packet.address ∧ policy = packet.policy
  then useBound policy scope retained brand asked packet.receipt else none

theorem select_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (w : Wire) (brand : Brand) (asked : Address Brand) (p : Selection Brand)
    (out : Tracked Scope (Address Brand)) :
    select policy scope w brand asked p = some out ↔
      asked = p.address ∧ policy = p.policy ∧
        p.receipt.fromWire = w ∧
        GeneralSourceRoleCstVisibleReceipt294.project policy scope w brand asked p.receipt.diagnostics =
          some out := by
  by_cases h : asked = p.address ∧ policy = p.policy
  · simp [select,h,use_bound_exact]
  · rw [select,ite_eq_right h]
    constructor
    · intro no; cases no
    · intro ok; exact False.elim (h ⟨ok.1,ok.2.1⟩)

theorem different_address_none {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (w : Wire) (brand : Brand) (asked : Address Brand) (p : Selection Brand)
    (neq : asked ≠ p.address) : select policy scope w brand asked p = none := by
  simp [select,neq]

theorem different_policy_none {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (w : Wire) (brand : Brand) (asked : Address Brand) (p : Selection Brand)
    (neq : policy ≠ p.policy) : select policy scope w brand asked p = none := by
  simp [select,neq]

end Yulang.GeneralSourceRoleCstSelectedSeal295
