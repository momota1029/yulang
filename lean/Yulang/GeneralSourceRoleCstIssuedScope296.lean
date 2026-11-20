import Yulang.GeneralSourceRoleCstCatalogOrder296

/-! Scope and revision are independently supplied, never inferred from
wire equality. Record equality is not an authenticity guarantee. -/
namespace Yulang.GeneralSourceRoleCstIssuedScope296
open GeneralSourceRoleCstNameCatalog296 (Catalog)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstWireBinding294 (same same_exact)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSelectedCompile295 (Boundary)
open GeneralSourceRoleCstCatalogExport296 (Failure Exported run)

structure Packet (S B Revision : Type) where
  retained : Wire
  scope : S
  selected : Address B
  policy : Policy
  revision : Revision
  fallbackArity : Nat
  catalog : Catalog

def checks {S B R : Type} [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (p : Packet S B R) (w : Wire) (scope : S) (a : Address B) (policy : Policy)
    (rev : R) (fallback : Nat) : Bool :=
  same p.retained w && decide (p.scope = scope) && decide (p.selected = a) &&
    decide (p.policy = policy) && decide (p.revision = rev) && decide (p.fallbackArity = fallback)

theorem checks_exact {S B R : Type} [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (p : Packet S B R) (w : Wire) (scope : S) (a : Address B) (policy : Policy) (rev : R) (fallback : Nat) :
    checks p w scope a policy rev fallback = true ↔ p.retained = w ∧ p.scope = scope ∧
      p.selected = a ∧ p.policy = policy ∧ p.revision = rev ∧ p.fallbackArity = fallback := by
  simp [checks,same_exact,and_assoc]

inductive Error where
  | mismatchedScope
  | selected (failure : Failure)
  deriving Repr, DecidableEq

def accept {S B R : Type} [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (p : Packet S B R) (w : Wire) (scope : S) (brand : B) (a : Address B) (policy : Policy)
    (rev : R) (sealed : Boundary S B) (fallback : Nat) : Except Error Exported :=
  if checks p w scope a policy rev fallback then
    (run policy scope w brand a sealed p.catalog fallback).mapError .selected
  else .error .mismatchedScope

theorem accept_exact {S B R : Type} [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (p : Packet S B R) (w : Wire) (scope : S) (brand : B) (a : Address B) (policy : Policy)
    (rev : R) (sealed : Boundary S B) (fallback : Nat) (out : Exported) :
    accept p w scope brand a policy rev sealed fallback = .ok out ↔
      checks p w scope a policy rev fallback = true ∧ run policy scope w brand a sealed p.catalog fallback = .ok out := by
  by_cases h : checks p w scope a policy rev fallback = true
  · cases r : run policy scope w brand a sealed p.catalog fallback <;>
      simp [accept,h,r,Except.mapError]
  · simp [accept,h]

theorem changed_revision_rejected {S B R : Type} [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (p : Packet S B R) (w : Wire) (scope : S) (brand : B) (a : Address B) (policy : Policy)
    (rev : R) (sealed : Boundary S B) (fallback : Nat) (h : p.revision ≠ rev) :
    accept p w scope brand a policy rev sealed fallback = .error .mismatchedScope := by
  have bad : ¬checks p w scope a policy rev fallback = true := fun ok => h (((checks_exact ..).mp ok).2.2.2.2.1)
  simp [accept,bad]

end Yulang.GeneralSourceRoleCstIssuedScope296
