import Yulang.GeneralSourceRoleCstSealOrigin295

/-! Consume one actually selected payload with the existing tracked
declaration exporter. The environment is explicit and is not derived from
wire equality, path equality, or a diagnostic receipt. -/
namespace Yulang.GeneralSourceRoleCstSelectedCompile295
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstSelectedSeal295 (Selection select)
open GeneralSourceRoleCstSealOrigin295 (selected_site)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleTrack292 (Tracked runTracked)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource)
open GeneralSourceMetadataExprDomain291 (bind_success)

structure Boundary (Scope Brand : Type) where
  allowedScope : Scope
  selected : Selection Brand

def handoff {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (sealed : Boundary Scope Brand) :
    Option (Tracked Scope (Address Brand)) :=
  if scope = sealed.allowedScope then select policy scope w brand a sealed.selected else none

def compile {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (sealed : Boundary Scope Brand)
    (env : Scope → Environment) (fallback : Nat) : Option RoleSource :=
  (handoff policy scope w brand a sealed).bind fun src => runTracked env fallback [src]

theorem handoff_exact {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (sealed : Boundary Scope Brand)
    (out : Tracked Scope (Address Brand)) :
    handoff policy scope w brand a sealed = some out ↔ scope = sealed.allowedScope ∧
      select policy scope w brand a sealed.selected = some out := by
  by_cases h : scope = sealed.allowedScope <;> simp [handoff,h]

theorem compile_exact {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (sealed : Boundary Scope Brand)
    (env : Scope → Environment) (fallback : Nat) (table : RoleSource) :
    compile policy scope w brand a sealed env fallback = some table ↔
      ∃ p, scope = sealed.allowedScope ∧
        select policy scope w brand a sealed.selected = some p ∧
        runTracked env fallback [p] = some table := by
  constructor
  · intro ok
    obtain ⟨p,got,done⟩ := bind_success ok
    obtain ⟨asked,one⟩ := (handoff_exact ..).mp got
    exact ⟨p,asked,one,done⟩
  · rintro ⟨p,scopeEq,got,done⟩
    unfold compile
    rw [(handoff_exact ..).mpr ⟨scopeEq,got⟩,Option.bind_some,done]

theorem rejected_never_compiles {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Boundary Scope Brand) (env : Scope → Environment) (fallback : Nat)
    (reject : handoff policy scope w brand a sealed = none) :
    compile policy scope w brand a sealed env fallback = none := by simp [compile,reject]

theorem compile_origin {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Boundary Scope Brand) (env : Scope → Environment) (fallback : Nat)
    (table : RoleSource) (ok : compile policy scope w brand a sealed env fallback = some table) :
    scope = sealed.allowedScope ∧ a = sealed.selected.address ∧
      ∃ p, p.atRole = a ∧ select policy scope w brand a sealed.selected = some p ∧
        runTracked env fallback [p] = some table := by
  obtain ⟨p,authorized,got,done⟩ := (compile_exact ..).mp ok
  obtain ⟨site,address,_⟩ := selected_site policy scope w brand a sealed.selected p got
  exact ⟨authorized,address,p,site,got,done⟩

end Yulang.GeneralSourceRoleCstSelectedCompile295
