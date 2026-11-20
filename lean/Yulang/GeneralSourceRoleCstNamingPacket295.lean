import Yulang.GeneralSourceRoleCstNamingTrace295

/-! Finite naming evidence can accompany a previously selected declaration.
It is checked against query identities, order, and exact reported values. -/
namespace Yulang.GeneralSourceRoleCstNamingPacket295
open GeneralSourceRoleCstNamingScope295 (symbolic compile_env_congr)
open GeneralSourceRoleCstNamingTrace295 (Trace capture captures_eq_agree)
open GeneralSourceRoleCstNamingRequests295 (Query)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff compile)
open GeneralSourceMetadataRoles291 (RoleSource)

def captureAt {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (nameEnv : S → Environment) : Option Trace :=
  (handoff policy scope w brand a sealed).bind fun p =>
    (symbolic p).map fun r => capture (nameEnv r.scope) r.role

structure FiniteBoundary (S B : Type) where
  selected : Boundary S B
  naming : Trace

def checked {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : FiniteBoundary S B)
    (actual : S → Environment) (fallback : Nat) : Option RoleSource :=
  if captureAt policy scope w brand a sealed.selected actual = some sealed.naming then
    compile policy scope w brand a sealed.selected actual fallback
  else none

theorem capture_at_exact {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (naming : S → Environment) (trace : Trace) :
    captureAt policy scope w brand a sealed naming = some trace ↔
    ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
      capture (naming r.scope) r.role = trace := by
  cases h : handoff policy scope w brand a sealed with
  | none => simp [captureAt,h]
  | some p =>
    cases r : symbolic p with
    | none => simp [captureAt,h,r]
    | some v => simp [captureAt,h,r]

theorem checked_exact {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : FiniteBoundary S B)
    (actual : S → Environment) (fallback : Nat) (table : RoleSource) :
    checked policy scope w brand a sealed actual fallback = some table ↔
      captureAt policy scope w brand a sealed.selected actual = some sealed.naming ∧
        compile policy scope w brand a sealed.selected actual fallback = some table := by
  by_cases h : captureAt policy scope w brand a sealed.selected actual = some sealed.naming <;>
    simp [checked,h]

theorem captured_naming_same_result {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (packet : FiniteBoundary S B)
    (reference actual : S → Environment) (fallback : Nat) (table : RoleSource)
    (named : captureAt policy scope w brand a packet.selected reference = some packet.naming)
    (ok : checked policy scope w brand a packet actual fallback = some table) :
    compile policy scope w brand a packet.selected reference fallback = some table := by
  obtain ⟨captured,built⟩ := (checked_exact ..).mp ok
  obtain ⟨p,r,comes,ready,obs⟩ := (capture_at_exact ..).mp named
  obtain ⟨q,u,comes',ready',obs'⟩ := (capture_at_exact ..).mp captured
  have same := Option.some.inj (comes.symm.trans comes')
  subst q
  have sameR := Option.some.inj (ready.symm.trans ready')
  subst u
  have agree := (captures_eq_agree ..).mp (obs.trans obs'.symm)
  have eq : compile policy scope w brand a packet.selected reference fallback =
      compile policy scope w brand a packet.selected actual fallback := by
    apply compile_env_congr
    intro p' h q' g
    have sameP := Option.some.inj (comes.symm.trans h)
    subst p'
    have sameQ := Option.some.inj (ready.symm.trans g)
    subst q'
    exact agree
  exact eq.trans built

end Yulang.GeneralSourceRoleCstNamingPacket295
