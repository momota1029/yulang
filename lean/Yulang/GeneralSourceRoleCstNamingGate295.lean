import Yulang.GeneralSourceRoleCstNamingWitness295

/-! Optional readback gate against an independently supplied naming map.
An identical map on selected reads is enough; neither map is authenticated. -/
namespace Yulang.GeneralSourceRoleCstNamingGate295
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleScopedExport292 (ScopedRole)
open GeneralSourceRoleLocalEnv292 (Agree)
open GeneralSourceRoleCstNamingWitness295 (roleMatch role_match_exact)
open GeneralSourceRoleCstNamingScope295 (symbolic compile_env_congr)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff compile)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceMetadataRoles291 (RoleSource)

def check {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (reference current : S → Environment) : Bool :=
  match handoff policy scope w brand a sealed with
  | none => false
  | some p =>
    match symbolic p with
    | none => false
    | some r => roleMatch (reference r.scope) (current r.scope) r.role

def checkedCompile {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (reference current : S → Environment) (fallback : Nat) : Option RoleSource :=
  if check policy scope w brand a sealed reference current then
    compile policy scope w brand a sealed current fallback
  else none

theorem check_exact {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (reference current : S → Environment) :
    check policy scope w brand a sealed reference current = true ↔
      ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
        Agree (reference r.scope) (current r.scope) r.role := by
  cases h : handoff policy scope w brand a sealed with
  | none => simp [check,h]
  | some p =>
    cases r : symbolic p with
    | none => simp [check,h,r]
    | some v => simp [check,h,r,role_match_exact]

theorem checked_reference_exact {S B : Type} [DecidableEq S] [DecidableEq B] (policy : Policy)
    (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (reference current : S → Environment) (fallback : Nat) (table : RoleSource) :
    checkedCompile policy scope w brand a sealed reference current fallback = some table ↔
      check policy scope w brand a sealed reference current = true ∧
      compile policy scope w brand a sealed reference fallback = some table := by
  by_cases h : check policy scope w brand a sealed reference current = true
  · obtain ⟨p,r,picked,ready,same⟩ := (check_exact ..).mp h
    have eq : compile policy scope w brand a sealed reference fallback =
      compile policy scope w brand a sealed current fallback := by
      apply compile_env_congr
      intro q got role parsed
      have eq := Option.some.inj (got.symm.trans picked)
      subst q
      have eqR := Option.some.inj (parsed.symm.trans ready)
      subst role
      exact same
    simp [checkedCompile,h,eq]
  · simp [checkedCompile,h]

end Yulang.GeneralSourceRoleCstNamingGate295
